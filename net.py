from optparse import OptionParser
from collections import defaultdict
from time import sleep, time

import argparse
import os
import json
from re import UNICODE
import sys
from random import randint
# IPaddress dependencies
from ipaddress import IPv6Network
import ipaddress

# Mininet dependencies
import mininet

from mininet.log import setLogLevel
from mininet.net import Mininet

from mininet.topo import SingleSwitchReversedTopo, Topo
from mininet.node import RemoteController, OVSBridge, Node, UserSwitch, OVSSwitch
from mininet.link import TCLink
from mininet.cli import CLI
from mininet.util import moveIntf, moveIntfNoRetry
from mininet.log import info, output, warn, setLogLevel
from mininet.term import makeTerms, runX11

# NetworkX dependencies
import networkx as nx
from networkx.readwrite import json_graph

# SRv6 dependencies
from srv6_topo_parser import *
#from srv6_utils import *
from srv6_generators import *
# SRv6 dependencies
from srv6_topo_parser import *
#from srv6_utils import *
from srv6_generators import *
#from srv6_net_utils import *
BASEDIR = os.path.abspath(os.path.dirname(__file__))
# nodes.sh file for setup of the nodes
NODES_SH = "/tmp/nodes.sh"
# Topology file
TOPOLOGY_FILE = "%s/topology.json" % BASEDIR
topologyFile = "%s/topo/5gTopo.json"  % BASEDIR
# Mapping node to management address
nodes_to_mgmt = {}
# Network topology
topology = nx.MultiDiGraph()


cost = 1
ra_interval = 10

# Create SRv6 topology and a management network for the hosts.

class SRv6Topo(Topo):

    # Init of the topology
    def __init__( self, topo="", **opts ):
        # Parse topology from json file
        parser = SRv6TopoParser(topo, verbose=False)
        parser.parse_data()
        # Save parsed data
        self.routers = parser.getRouters()
        p_routers_properties = parser.getRoutersProperties()
        self.core_links = parser.getCoreLinks()
        p_core_links_properties = parser.getCoreLinksProperties()        
        # Properties generator
        generator = PropertiesGenerator()       
        # Second step is the generation of the nodes parameters
        routers_properties = generator.getRoutersProperties(self.routers)
        self.routers_properties = p_routers_properties        
        # Assign mgmt ip to the mgmt station
        # Third step is the generation of the links parameters
        core_links_properties = [] 
        for core_link in self.core_links:
            core_links_properties.append(generator.getLinksProperties([core_link]))
        for core_link_properties, p_core_link_properties in zip(core_links_properties, p_core_links_properties):
            p_core_link_properties['iplhs'] = core_link_properties[0].iplhs
            p_core_link_properties['iprhs'] = core_link_properties[0].iprhs
            p_core_link_properties['net'] = core_link_properties[0].net
        self.core_links_properties = p_core_links_properties
        # Init steps
        Topo.__init__( self, **opts )

    # Build the topology using parser information
    
    def build( self, *args, **params):
        # Mapping nodes to nets
        nodes_to_nets = defaultdict(list)
        # Init steps
        Topo.build( self, *args, **params )
        # Add routers
        numberofgnb = 1
        numberofue = 1
        n = 1
        for router, router_properties in zip(self.routers, self.routers_properties):
           # Add the UPF to the topology
            i = 0

            self.addSwitch(name=router, inNamespace=True, cls=UserSwitch, nets=[])
            for i in range(numberofgnb):
                rrh = 'RRH%s%s'%(router[3], i + 1 )
                self.addSwitch(name=rrh, inNamespace=False, cls=OVSSwitch,  nets=[],  failMode='standalone')
                self.addLink(router,rrh)
                j = 0
                for j in range(numberofue):
                    ue = 'ue%s'%(n)
                    self.addHost(ue)
                    self.addLink(rrh,ue)  
                    n+=1
        
            topology.add_node(router, type="router")
    
        # Iterate over the core links and generate them
        for core_link, core_link_properties in zip(self.core_links, self.core_links_properties):
            # Get the left hand side of the pair
            lhs = core_link[0]
            # Get the right hand side of the pair
            rhs = core_link[1]
            # Create the core link 
            self.addLink(lhs, rhs, bw=core_link_properties['bw'],
                delay=core_link_properties['delay'])
            # Get Port number
            portNumber = self.port(lhs, rhs)
           
            # Create lhs_intf
            lhsintf = "%s-eth%d" % (lhs, portNumber[0])
            lhIPv6 =  "20%s%s::1/64"%( lhs[3] , rhs[3] )        
            # Create rhs_intf
            rhsintf = "%s-eth%d" % (rhs, portNumber[1])
            rhIPv6 = "20%s%s::2/64"%( lhs[3] , rhs[3] )
            # Assign a data-plane net to this link
            net = core_link_properties['net']
            # Get lhs ip
            lhsip =  "%s/%d" % (core_link_properties['iplhs'], NetAllocator.prefix)
            # Get rhs ip
            rhsip =  "%s/%d" % (core_link_properties['iprhs'], NetAllocator.prefix)
            # Add edge to the topology
            topology.add_edge(lhs, rhs, lhs_intf=lhsintf, rhs_intf=rhsintf, lhs_ip=lhsip, rhs_ip=rhsip)
            # Add the reverse edge to the topology
            topology.add_edge(rhs, lhs, lhs_intf=rhsintf, rhs_intf=lhsintf, lhs_ip=rhsip, rhs_ip=lhsip)
            # Save net
            lhsnet = {'intf':lhsintf, 'ip':lhIPv6, 'net':net}
            rhsnet = {'intf':rhsintf, 'ip':rhIPv6, 'net':net}
            self.nodeInfo(lhs)['nets'].append(lhsnet)
            self.nodeInfo(rhs)['nets'].append(rhsnet)


def moveIntf( intf, oldSwitch, newSwitch, port=None, rename=True ):
    oldSwitch.detach( intf )
    newSwitch.addIntf( intf)
    intf.node = newSwitch
    '''if rename:
        OVSSwitch.renameIntf( intf )'''
    port = newSwitch.ports[ intf ]
    if port:
        if newSwitch.isOldOVS():
            newSwitch.cmd( 'ovs-vsctl add-port', newSwitch, intf )
        else:
            newSwitch.cmd( 'ovs-vsctl add-port', newSwitch, intf,
                        '-- set Interface', intf,
                        'ofport_request=%s' % port )
        #newSwitch.validatePort( intf )



def moveHost( host, oldSwitch, newSwitch, newPort=None ):
    "Move a host from old switch to new switch"
    hintf, sintf = host.connectionsTo( oldSwitch )[ 0 ]
    moveIntf( sintf, oldSwitch, newSwitch, port=newPort )
    return hintf, sintf
    
def mobility(net):
    info( '* Simple mobility test\n' )
    ue, oldGnb = net.get( 'ue1', 'gnb11' )
    ue.cmd("poff -a")
    new = net['gnb12']
    port = randint( 10, 20 )
    info( '* Moving', ue, 'from', oldGnb, 'to', new, 'port', port, '\n' )
    hintf, sintf = moveHost( ue, oldGnb, new, newPort=port)
    #ue.cmd("pppoe-connect %s/%s.conf &" % (dir, ue.name))
    while True:
        intf = ue.cmd("ls /sys/class/net")
        up = ue.cmd('ifconfig -a ppp0')
        if intf.find('ppp0') != -1 and up.find('UP') != -1:          
            ue.cmd("ifconfig ppp0 inet6 add 2001:%s::3/127"% ue.name[2])
            ue.cmd("sudo ip -6 route add 2001:%s::2 dev ppp0"% ue.name[2])
            ue.cmd("sudo ip -6 route add default via 2001:%s::2"% ue.name[2])
            break
        
        #ueintf , gintf = ue.connectionsTo( new )[ 0 ]
    print(hintf, sintf)
    '''for s in 2, 3, 1:
        new = net[ 's%d' % s ]
        port = randint( 10, 20 )
        info( '* Moving', h1, 'from', old, 'to', new, 'port', port, '\n' )
        hintf, sintf = moveHost( h1, old, new, newPort=port)
        info( '*', hintf, 'is now connected to', sintf, '\n' )
        info( '* Clearing out old flows\n')
        for sw in net.switches:
            sw.dpctl( 'del-flows')
        info( '* New network:\n')
        printConnections( net.switches )
        info( '* Testing connectivity:\n' )
        net.pingAll()
        old = new
    net.stop()'''

def dump():
  # Json dump of the topology
  with open(TOPOLOGY_FILE, 'w') as outfile:
    # Get json topology
    json_topology = json_graph.node_link_data(topology)
    # Convert links
    json_topology['links'] = [
        {
           """ 'source': json_topology['nodes'][link['source']]['id'],
            'target': json_topology['nodes'][link['target']]['id'], """
            'lhs_intf': link['lhs_intf'], 
            'rhs_intf': link['rhs_intf'],
            'lhs_ip': str((ipaddress.ip_interface(link['lhs_ip'])).ip),
            'rhs_ip': str((ipaddress.ip_interface(link['rhs_ip'])).ip)
        }
        for link in json_topology['links']]
    # Dump the topology
    json.dump(json_topology, outfile, sort_keys = True, indent = 2)
  # Dump for nodes.sh
  with open(NODES_SH, 'w') as outfile:
    # Create header
    nodes = "declare -a NODES=("
    # Iterate over management ips
    for node, ip in nodes_to_mgmt.iteritems():
      # Add the nodes one by one
      nodes = nodes + "%s " % ip
    if nodes_to_mgmt != {}:
        # Eliminate last character
        nodes = nodes[:-1] + ")\n"
    else:
        nodes = nodes + ")\n"
    # Write on the file
    outfile.write(nodes)

# Utility function to shutdown the emulation
def stopAll():
    # Clean Mininet emulation environment
    os.system('sudo mn -c')
    # Kill all the started daemons
    os.system('sudo killall sshd zebra ospf6d')
    # Restart root ssh daemon
    os.system('service sshd restart')
    os.system("rm -rf /ospfdsrv6")

# Utility function to deploy Mininet topology

    
def ospfConfig(net):
    dirs = ['/var/mininet']
    nets = []
    first = True
    i = 0
    for router in net.switches:
        if router.name[0] == 'U' or router.name[0] == 'D' or router.name[0] == 'G':                
            dir = "%s/ospf6/%s" % (BASEDIR,router.name)
            if not os.path.exists(dir):
                os.makedirs(dir)
            for intf in net.topo.nodeInfo(router.name)['nets']:
                # Remove any configured address
                router.cmd('ifconfig %s 0' %intf)
               
            # Enable IPv6 forwarding
            router.cmd("sysctl -w net.ipv6.conf.all.forwarding=1")
            # Enable SRv6 on the interfaces
            router.cmd("sysctl -w net.ipv6.conf.all.seg6_enabled=1")
            if router.name == 'GNB1': 
                router.cmd(" pppoe-server -F -I %s-eth1 &"% router.name)
                router.cmd(" pppoe-server -F -I %s-eth2 &"% router.name)
                #router.cmd("ifconfig %s-eth1 inet6 add 2001:30::31/64"%(router.name))
                #router.cmd("ifconfig %s-eth2 inet6 add 2001:30::32/64"%(router.name))
                sleep(3)               
                #ue1, ue2, ue3, ue4 = net.get( 'ue1','ue2','ue3','ue4' )   
                ue =  net.get( 'ue1')          
                #for ue in ue1: 
                ppp_dir = "%s/ppp" % (BASEDIR)
                ue.cmd("sysctl -w net.ipv4.ip_forward=1")
                ue.cmd("sysctl -w net.ipv6.ip_forward=1")
                ue.cmd("sysctl -w net.ipv6.conf.all.forwarding=1")
                ue.cmd("sysctl -w net.ipv6.conf.all.autoconf=1")
                ue.cmd("sysctl -w net.ipv6.conf.default.autoconf=1")
                ue.cmd("sysctl -w net.ipv6.conf.all.accept_ra=1")
                ue.cmd("sysctl -w net.ipv6.conf.default.accept_ra=1")
                ue.cmd("sysctl -w net.ipv6.conf.all.accept_redirects=1")
                ue.cmd("sysctl -w net.ipv6.conf.all.router_solicitations=1")
                ue.cmd("sysctl -w net.ipv6.conf.default.proxy_ndp=1")
                ue.cmd("sysctl -w net.ipv6.conf.all.proxy_ndp=1")
                ue.cmd("sysctl -w net.ipv6.conf.default.forwarding=1")
                ue.cmd("sysctl -w net.ipv6.conf.all.forwarding=1")
                ue.cmd("sysctl -w net.ipv6.conf.all.seg6_enabled=1")
                '''with open("%s/h1.conf" % BASEDIR, 'r') as ppp:
                    text = ppp.read()
                ppp.close()
                with open("%s/%s.conf" % (dir, ue.name), 'w') as ppp:
                    ppp.write(text)
                    ppp.write( "ETH='%s-eth0' \n"% ue.name)
                    ppp.write( "USER='%s'"% ue.name)
                ppp.close()'''
                ue.cmd("pppoe-connect %s/%s.conf &" % (ppp_dir, ue.name))
                sleep(3)        
                ue.cmd("ifconfig ppp0 inet6 add 2001:%s::3/127"% ue.name[2])
                #ue.cmd("ifconfig %s-eth0 inet6 add 2001:30::%s/64"%(ue.name, ue.name[2]))
                ue.cmd("sudo ip -6 route add 2001:%s::2 dev ppp0"% ue.name[2])
                ue.cmd("sudo ip -6 route add default via 2001:%s::2"% ue.name[2])
                '''ue.cmd("ifconfig ppp0 inet6 add 2001:%s::3/64"% ue.name[2])
                ue.cmd("ifconfig %s-eth0 inet6 add 2001:30::%s/64"%(ue.name, ue.name[2]))
                ue.cmd("sudo ip -6 route add 2001:30::31 dev ue1-eth0")
                ue.cmd("sudo ip -6 route add default via 2001:30::31")'''
        
                

            if router.name == 'DNN3': 
                ue5 = net.get('ue3')            
                ppp_dir = "%s/ppp" % (BASEDIR)
                ue5.cmd("sysctl -w net.ipv4.ip_forward=1")
                ue5.cmd("sysctl -w net.ipv6.ip_forward=1")
                ue5.cmd("sysctl -w net.ipv6.conf.all.forwarding=1")
                ue5.cmd("sysctl -w net.ipv6.conf.all.autoconf=1")
                ue5.cmd("sysctl -w net.ipv6.conf.default.autoconf=1")
                ue5.cmd("sysctl -w net.ipv6.conf.all.accept_ra=1")
                ue5.cmd("sysctl -w net.ipv6.conf.default.accept_ra=1")
                ue5.cmd("sysctl -w net.ipv6.conf.all.accept_redirects=1")
                ue5.cmd("sysctl -w net.ipv6.conf.all.router_solicitations=1")
                ue5.cmd("sysctl -w net.ipv6.conf.default.proxy_ndp=1")
                ue5.cmd("sysctl -w net.ipv6.conf.all.proxy_ndp=1")
                ue5.cmd("sysctl -w net.ipv6.conf.default.forwarding=1")
                ue5.cmd("sysctl -w net.ipv6.conf.all.forwarding=1")
                ue5.cmd("sysctl -w net.ipv6.conf.all.seg6_enabled=1")
                ue5.cmd("sudo ifconfig %s-eth0 inet6 add 2000::1/64" % ue5.name)
                ue5.cmd("sudo ip -6 route add 2000::2 dev ue4-eth0")
                ue5.cmd("sudo ip -6 route add default via 2000::2")


                '''ue5.cmd("ifconfig ue5-eth0 inet6 add 2000::1/64")
                ue5.cmd("sudo ip -6 route add 2000::2/64 dev ue5-eth0")
                ue5.cmd("sudo ip -6 route add default dev ue5-eth0")
                with open("%s/h1.conf" % BASEDIR, 'r') as ppp:
                    text = ppp.read()
                ppp.close()
                with open("%s/%s.conf" % (dir, ue.name), 'w') as ppp:
                    ppp.write(text)
                    ppp.write( "ETH='%s-eth0' \n"% ue.name)
                    ppp.write( "USER='%s'"% ue.name)
                ppp.close()
                ue.cmd("pppoe-connect %s/%s.conf &" % (dir, ue.name))
                sleep(3)'''


            #router.cmd("ifconfig %s-eth1 inet6 add 2001:30::31/64"%(router.name))
            #router.cmd("ifconfig %s-eth2 inet6 add 2001:30::32/64"%(router.name))
            # Disable RA accept
            router.cmd("sysctl -w net.ipv6.conf.all.accept_ra=1")
            zebra = open("%s/zebra.conf" % dir, 'w')
            ospfd = open("%s/ospf6d.conf" % dir, 'w')
            ospfd.write("! -*- ospf6 -*-\n!\nhostname %s\n" % router.name)
            ospfd.write("password srv6\nlog file %s/ospf6d.log\n!\n" % dir)
            zebra.write("! -*- zebra -*-\n!\nhostname %s\n" %router.name)
            zebra.write("password srv6\nenable password srv6\nlog file %s/zebra.log\n!\n" % dir)
            for intf in net.topo.nodeInfo(router.name)['nets']:
                cost = 1
                ra_interval = 10
                router.cmd("sysctl -w net.ipv6.conf.%s.forwarding=1" %intf['intf'])
                # Enable SRv6 on the interface
                router.cmd("sysctl -w net.ipv6.conf.%s.seg6_enabled=1" %intf['intf'])
                ospfd.write("interface %s\n  ipv6 ospf6 cost %s\n  ipv6 ospf6 hello-interval %s\n  ipv6 ospf6 dead-interval 40 \n  ipv6 ospf6 retransmit-interval 5\n  ipv6 ospf6 network point-to-point \n"%(intf['intf'], cost, 10))
                zebra.write("interface %s\n  link-detect\n  no ipv6 nd suppress-ra\n  ipv6 nd ra-interval %s\n  ipv6 address %s \n"
                %(intf['intf'], ra_interval, intf['ip']))
            if router.name == 'GNB1':
                #router.cmd("sudo ifconfig UPF1-eth1 inet6 add 2001:30::31/64")  
                router.cmd("sysctl -w net.ipv6.conf.%s.forwarding=1" %'UPF1-eth1')
                # Enable SRv6 on the interface
                router.cmd("sysctl -w net.ipv6.conf.%s.seg6_enabled=1" %'UPF1-eth1')
            
            if router.name == 'DNN3':
                '''ospfd.write("interface %s\n  ipv6 ospf6 cost %s\n  ipv6 ospf6 hello-interval %s\n  ipv6 ospf6 dead-interval 40 \n  ipv6 ospf6 retransmit-interval 5\n"%('DNN2-eth1', cost, 10))
                zebra.write("interface %s\n  link-detect\n  no ipv6 nd suppress-ra\n  ipv6 nd ra-interval %s\n  ipv6 address %s \n"
                        %('DNN2-eth1', ra_interval, '2000::2/64'))'''
                router.cmd("sudo ifconfig DNN3-eth1 inet6 add 2000::2/64")        
                router.cmd("sysctl -w net.ipv6.conf.%s.forwarding=1" %'DNN2-eth1')
                # Enable SRv6 on the interface
                router.cmd("sysctl -w net.ipv6.conf.%s.seg6_enabled=1" %'DNN2-eth1')
                
            #ospfd.write("interface ppp0  ipv6 ospf6 cost %s\n  ipv6 ospf6 hello-interval %s\n  ipv6 ospf6 dead-interval 40 \n  ipv6 ospf6 retransmit-interval 5\n"%( cost, 10))
            #zebra.write("interface ppp0  link-detect\n  no ipv6 nd suppress-ra\n  ipv6 nd ra-interval %s\n  ipv6 address %s \n"  %(ra_interval, intf['ip']))
            # Finishing ospf6d conf
            routerid = '%s.0.0.%s'%(router.name[3], router.name[3])
            ospfd.write("router ospf6 \n  router-id %s\n redistribute connected \n  " %routerid)
            #ospfd.write("area 0.0.0.0 range %s \n" %RANGE_FOR_AREA_0)
            #Iterate again over the nets to finish area part

            for intf in net.topo.nodeInfo(router.name)['nets']:
                ospfd.write("  interface %s area 0.0.0.0\n" %(intf['intf']))
                
            '''if router.name == 'GNB1':
                ospfd.write("  interface %s area 0.0.0.0\n" %('UPF1-eth1'))
               
            if router.name == 'DNN2':
                ospfd.write("  interface %s area 0.0.0.0\n" %('DNN2-eth1'))'''

                #ospfd.write("!\n")
            # Right permission and owners
            router.cmd("chown quagga.quaggavty %s/*.conf" %dir)
            router.cmd("chown quagga.quaggavty %s/." %dir)
            router.cmd("chmod 640 %s/*.conf" %dir)
            router.cmd("sysctl -w net.ipv4.ip_forward=1")
            router.cmd("sysctl -w net.ipv6.ip_forward=1")
            router.cmd("sysctl -w net.ipv6.conf.all.autoconf=1")
            router.cmd("sysctl -w net.ipv6.conf.default.autoconf=1")
            router.cmd("sysctl -w net.ipv6.conf.all.accept_ra=1")
            router.cmd("sysctl -w net.ipv6.conf.default.accept_ra=1")
            router.cmd("sysctl -w net.ipv6.conf.all.accept_redirects=1")
            router.cmd("sysctl -w net.ipv6.conf.all.router_solicitations=1")
            router.cmd("sysctl -w net.ipv6.conf.default.proxy_ndp=1")
            router.cmd("sysctl -w net.ipv6.conf.all.proxy_ndp=1")
            router.cmd("sysctl -w net.ipv6.conf.default.forwarding=1")
            router.cmd("sysctl -w net.ipv6.conf.all.forwarding=1")
            router.cmd("sysctl -w net.ipv6.conf.all.seg6_enabled=1")

            # Starting daemons
            ospfd.close()
            zebra.close()
            router.cmd("/usr/sbin/zebra  -f %s/zebra.conf -d -z %s/zebra.sock -i %s/zebra.pid" %(dir, dir, dir))
            router.cmd("/usr/sbin/ospf6d -f %s/ospf6d.conf -d -z %s/zebra.sock -i %s/ospf6d.pid" %(dir, dir, dir))
            i = i + 1
        router.cmd("sysctl -w net.ipv4.ip_forward=1")
        router.cmd("sysctl -w net.ipv6.ip_forward=1")
        router.cmd("sysctl -w net.ipv6.conf.all.autoconf=1")
        router.cmd("sysctl -w net.ipv6.conf.default.autoconf=1")
        router.cmd("sysctl -w net.ipv6.conf.all.accept_ra=1")
        router.cmd("sysctl -w net.ipv6.conf.default.accept_ra=1")
        router.cmd("sysctl -w net.ipv6.conf.all.accept_redirects=1 ")
        router.cmd("sysctl -w net.ipv6.conf.all.router_solicitations=1")
        router.cmd("sysctl -w net.ipv6.conf.default.proxy_ndp=1")
        router.cmd("sysctl -w net.ipv6.conf.all.proxy_ndp=1")
        router.cmd("sysctl -w net.ipv6.conf.default.forwarding=1")
        router.cmd("sysctl -w net.ipv6.conf.all.forwarding=1")
        router.cmd("sysctl -w net.ipv6.conf.all.seg6_enabled=1")

def deploy(  ):
    topo = SRv6Topo(topo=topologyFile)
    # Create Mininet net
    net = Mininet(topo=topo, link=TCLink,
            build=False, controller=None)
    net.build()
    net.start()
    ospfConfig(net)
    n1, server, gnb, upf, dn  = net.get( 'ue1', 'ue3', 'GNB1', 'UPF2','DNN3')
    net.terms += makeTerms( [ n1 ], term = 'xterm' )
    net.terms += makeTerms( [ server ], term = 'xterm' )
    net.terms += makeTerms( [ gnb ], term ='xterm' )
    net.terms += makeTerms( [ upf], term = 'xterm' )
    net.terms += makeTerms( [ dn], term = 'xterm' )
    #sleep(60)
    #pdn_establishment(net)
    #mobility(net)
    # dump information
    dump() 
    CLI(net)
    # Stop topology
    net.stop()
    stopAll()
def sid_generator(ue):
    ue_ip = ue.cmd('ip -6 -o addr show up primary scope global | while read -r num dev fam addr rest; do echo ${addr%/*}; done')[0:9]
    ip = ue_ip[5]
    print(ip)
    return {  
              'ue_ip': ue_ip,
              'uplink': '1111::%s' % ip,
              'downlink': '2222::%s' % ip 
           }

def pdn_establishment(net):
    ue, gnb, upf = net.get('ue1','GNB1', 'UPF2')
    n2_intf1, n2_intf2 = gnb.connectionsTo( upf )[ 0 ]
    upf_ip = upf.cmd('ip -6 -o addr show %s primary scope global | while read -r num dev fam addr rest; do echo %s done' % (n2_intf2.name, '${addr%/*};'))[0:7]
    gnb_ip = gnb.cmd('ip -6 -o addr show %s primary scope global | while read -r num dev fam addr rest; do echo %s done' % (n2_intf1.name, '${addr%/*};'))[0:7]
    sid = sid_generator(ue)
    print(sid, upf_ip)
    upf.cmd('ifconfig lo up')
    upf.cmd('ifconfig lo inet6 add %s/32' % sid['uplink'])
    gnb.cmd('ifconfig lo up')
    gnb.cmd('ifconfig lo inet6 add %s/32' % sid['downlink'])
    #gnb.cmd(' echo 100     %spdn >> /etc/iproute2/rt_tables' % ue.name)
    gnb.cmd('ip -6 rule add from %s table %s priority 0' % (sid['ue_ip'],'ue1pdn'))
    gnb.cmd("ip -6 route add default via %s encap seg6 mode encap segs %s table %s"  % (upf_ip, sid['uplink'] ,'ue1pdn' ))
    #upf.cmd('ip -6 rule add to %s table %s priority 0' % (sid['ue_ip'],'ue1pdn'))
    #upf.cmd("ip -6 route add %s via %s encap seg6 mode encap segs %s table %s"  % (sid['ue_ip'],'2012::1',sid['uplink'],'2023::2','ue1pdn' ))

    #ue.cmd("sudo ip -6 route add 2001:30::31 dev ue1-eth0")
    '''ue.cmd("sudo ip -6 route add default via 2012::2  encap seg6 mode encap segs %s matric 5" % sid['uplink'] )
    gnb.cmd("ip -6 route add 2012::2/64 dev GNB1-eth2 encap seg6 mode encap segs %s matric 5" % sid['uplink'])
    upf.cmd("ip -6 route add 2012::1/64 dev UPF2-eth2 encap seg6 mode encap segs %s matric 5" % sid['downlink'])'''

    
        

# Parse command line options and dump results
def parseOptions():
    parser = OptionParser()
    # IP of RYU controller
    parser.add_option('--controller', dest='controller', type='string', default="127.0.0.1",
                      help='IP address of the Controlle instance')
    # Topology json file
    parser.add_option('--topology', dest='topology', type='string', default="example_srv6_topology.json",
                      help='Topology file')
    # Clean all useful for rdcl stop action
    parser.add_option('--stop-all', dest='clean_all',action='store_true', help='Clean all mininet environment')
    # Start without Mininet prompt - useful for rdcl start action
    parser.add_option('--no-cli', dest='no_cli',action='store_true', help='Do not show Mininet CLI')
    # Parse input parameters
    (options, args) = parser.parse_args()
    # Done, return
    return options

if __name__ == '__main__':
    deploy()