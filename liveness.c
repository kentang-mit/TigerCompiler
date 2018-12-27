#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"
#include "string.h"

G_nodeList vis_seq = NULL;
G_table mark_table, in_live_table, out_live_table;

static void Live_init(){
    mark_table = G_empty();
    in_live_table = G_empty();
    out_live_table = G_empty();
}

static void enterLiveMap(G_table t, G_node flowNode, Temp_tempList temps){
    G_enter(t, flowNode, temps);
}

static Temp_tempList lookupLiveMap(G_table t, G_node flowNode){
    return (Temp_tempList)G_look(t, flowNode);
}

static void Live_DFS(G_node n){
    G_nodeList successors = G_succ(n);
    for(G_nodeList l = successors; l; l = l->tail){
    }
}

//for debugging
static void printTemp(Temp_temp t){
    printf("t%d ", Temp_int(t));
}
static void printTempList(Temp_tempList l){
    for(Temp_tempList t = l; t; t = t->tail) printf("%d ", Temp_int(t->head));
    printf("\n");
}

static Temp_tempList copy_tempList(Temp_tempList given){
    Temp_tempList first = NULL, last = NULL;
    for(Temp_tempList p = given; p; p = p->tail){
        if(!first) first = Temp_TempList(p->head, NULL);
        else if(!last){
            first->tail = last = Temp_TempList(p->head, NULL);
        }
        else last = last->tail = Temp_TempList(p->head, NULL);
    }
    return first;
}

static int compare_tempList(Temp_tempList t1, Temp_tempList t2){
    Temp_tempList p1 = t1, p2 = t2;
    int p1len = 0;
    Temp_map m = Temp_empty();
    for(; p1; p1 = p1->tail, p1len++){
        Temp_enter(m, p1->head, String(""));
    }
    int p2len = 0;
    for(; p2; p2 = p2->tail, p2len++){
        if(!Temp_look(m, p2->head)) return 0;
    }
    return p1len==p2len;
}

static Temp_tempList diff_tempList(Temp_tempList t1, Temp_tempList t2){
    Temp_tempList p1, p2;
    Temp_tempList first = NULL, last = NULL;
    //use hash map to accelerate
    Temp_map m = Temp_empty();
    for(p2 = t2; p2; p2 = p2->tail){
        Temp_enter(m, p2->head, String(""));
    }
    for(p1 = t1; p1; p1 = p1->tail){
       Temp_temp cur1 = p1->head;
        if(!Temp_look(m, cur1)){
            if(!first) first = Temp_TempList(cur1, NULL);
            else if(!last){
                first->tail = last = Temp_TempList(cur1, NULL);
            }
            else last = last->tail = Temp_TempList(cur1, NULL);
        }
    }
    /*
    printf("T1: "); printTempList(t1);
    printf("T2: "); printTempList(t2);
    printf("DIFF: "); printTempList(first);
    */
    return first;
}

static Temp_tempList union_tempList(Temp_tempList t1, Temp_tempList t2){
    Temp_tempList p1, p2;
    Temp_tempList first = NULL, last = NULL;
    //use hash map to accelerate
    Temp_map m = Temp_empty();
    for(p1 = t1; p1; p1 = p1->tail){
       Temp_temp cur1 = p1->head;
       Temp_enter(m, cur1, String("")); 
       if(!first) first = Temp_TempList(cur1, NULL);
       else if(!last){
            first->tail = last = Temp_TempList(cur1, NULL);
       }
       else last = last->tail = Temp_TempList(cur1, NULL);
    }
    for(p2 = t2; p2; p2 = p2->tail){
       Temp_temp cur2 = p2->head;
       if(Temp_look(m, cur2)) continue;
       Temp_enter(m, cur2, String("")); 
       if(!first) first = Temp_TempList(cur2, NULL);
       else if(!last){
            first->tail = last = Temp_TempList(cur2, NULL);
       }
       else last = last->tail = Temp_TempList(cur2, NULL);
    }
    return first;
}

static Temp_tempList intersect_tempList(Temp_tempList t1, Temp_tempList t2){
    Temp_tempList p1, p2;
    Temp_tempList first = NULL, last = NULL;
    //use hash map to accelerate
    Temp_map m = Temp_empty();
    for(p1 = t1; p1; p1 = p1->tail){
       Temp_temp cur1 = p1->head;
       Temp_enter(m, cur1, String("")); 
    }
    for(p2 = t2; p2; p2 = p2->tail){
       Temp_temp cur2 = p2->head;
       if(!Temp_look(m, cur2)) continue;
       Temp_enter(m, cur2, String("")); 
       if(!first) first = Temp_TempList(cur2, NULL);
       else if(!last){
            first->tail = last = Temp_TempList(cur2, NULL);
       }
       else last = last->tail = Temp_TempList(cur2, NULL);
    }
    return first;
}

static Temp_tempList Live_succ_union(G_node n){
    //out[n] = U{s in succ[n]} in[s]
    G_nodeList n_succ = G_succ(n);
    Temp_tempList rev_list = NULL;
    //use hash map to accelerate
    Temp_map m = Temp_empty();
    for(G_nodeList nl = n_succ; nl; nl = nl->tail){
        G_node cur_n = nl->head;
        Temp_tempList cur_live_in = lookupLiveMap(in_live_table, cur_n);
        for(Temp_tempList lst = cur_live_in; lst; lst = lst->tail){
            if(Temp_look(m,lst->head)) continue;
            Temp_enter(m,lst->head, String(""));
            rev_list = Temp_TempList(lst->head, rev_list);
        }
    }
    Temp_tempList ret_list = NULL;
    for(Temp_tempList lst = rev_list; lst; lst = lst->tail) ret_list = Temp_TempList(lst->head, ret_list);
    return ret_list;
}



Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
}


Temp_temp Live_gtemp(G_node n) {
	return (Temp_temp)G_nodeInfo(n);
}


//typedef TAB_table Live_table;
Live_table Live_empty(void) {
  return TAB_empty();
}

void Live_enter(Live_table t, Temp_temp temp, void *value)
{
  TAB_enter(t, temp, value);
}

void *Live_look(Live_table t, Temp_temp temp)
{
  return TAB_look(t, temp);
}

G_node Live_lookupTempMap(Live_table t, Temp_temp temp){
    return (G_node)Live_look(t, temp);
}

Live_table m;

Live_table Live_getTable(){
    return m;
}

struct Live_graph Live_liveness(G_graph flow) {
	//TBD: topological sort
	struct Live_graph lg;
    Live_init();
    G_graph live = G_Graph();
    
    Live_moveList live_ml_first = NULL, live_ml_last = NULL;
    
    //naive, just reverse the node list.
    vis_seq = NULL;
    for(G_nodeList p = G_nodes(flow); p; p = p->tail){
        vis_seq = G_NodeList(p->head, vis_seq);
    }

    G_nodeList nodes = vis_seq;
    for(G_nodeList nl = nodes; nl; nl = nl->tail){
        if(nl->tail){
            enterLiveMap(in_live_table, nl->head, NULL);
            enterLiveMap(out_live_table, nl->head, NULL);
        }
        else{
            //printTempList(F_MachineRegisters());
            enterLiveMap(in_live_table, nl->head, NULL);
            //machine registers...?
            //enterLiveMap(out_live_table, nl->head, F_MachineRegisters());
        }
    }
    //Algorithm 10.1
    int cnt = 0;
    while(1){
        cnt++;
        int to_continue = cnt>1?0:1; //a trick. Otherwise only run 1 round of while.
        for(G_nodeList nl = nodes; nl; nl = nl->tail){
            G_node n = nl->head;
            Temp_tempList n_in = lookupLiveMap(in_live_table, n);
            Temp_tempList n_out = lookupLiveMap(out_live_table, n);
            Temp_tempList n_in_backup = copy_tempList(n_in);
            Temp_tempList n_out_backup = copy_tempList(n_out);
            Temp_tempList n_use = FG_use(n);
            Temp_tempList n_def = FG_def(n);
            //n_out = Live_succ_union(n);
            n_out = union_tempList(n_out, Live_succ_union(n));
            n_in = union_tempList(n_use, diff_tempList(n_out, n_def));
            //need to enter into the live map
            enterLiveMap(in_live_table, n, n_in);
            enterLiveMap(out_live_table, n, n_out);
                    
            int cmp1 = compare_tempList(n_in, n_in_backup);
            int cmp2 = compare_tempList(n_out, n_out_backup);
            
        }
        if(!to_continue) break;
    }
    //form the liveness graph and move list, defined globally
    m = Live_empty();
    //nodes: belong to the flow graph
    for(G_nodeList nl = nodes; nl; nl = nl->tail){
        G_node n = nl->head;
        AS_instr cur_instr = (AS_instr)G_nodeInfo(n);
        if(cur_instr->kind == I_MOVE){
            Temp_tempList dsts = cur_instr->u.MOVE.dst, srcs = cur_instr->u.MOVE.src;
            Temp_temp dst = dsts->head;
            Temp_temp src = srcs->head;
            G_node dst_node = Live_lookupTempMap(m, dst);
            if(!dst_node){
                dst_node = G_Node(live, dst);
                Live_enter(m, dst, dst_node);
            }
            G_node src_node = Live_lookupTempMap(m, src);            
            if(!src_node){
                src_node = G_Node(live, src);
                Live_enter(m, src, src_node);
            }
            
            if(!live_ml_first) live_ml_first = Live_MoveList(src_node, dst_node, NULL);
            else if(!live_ml_last){
                live_ml_first->tail = live_ml_last = Live_MoveList(src_node, dst_node, NULL);
            }
            else{
                live_ml_last = live_ml_last->tail = Live_MoveList(src_node, dst_node, NULL);
            }
            continue;
        }
        Temp_tempList n_in = lookupLiveMap(in_live_table, n);
        G_nodeList in_nodes = NULL;
        //in nodes
        for(Temp_tempList p = n_in; p; p = p->tail){
            G_node cur = Live_lookupTempMap(m, p->head);
            if(!cur){
                cur = G_Node(live, p->head);
                Live_enter(m, p->head, cur);
            }
            in_nodes = G_NodeList(cur, in_nodes);
        }
        for(G_nodeList i = in_nodes; i; i = i->tail){
            for(G_nodeList j = i->tail; j; j = j->tail){
                G_node node1 = i->head, node2 = j->head;
                G_addEdge(node1, node2);
            }
        }
        //out nodes
        Temp_tempList n_out = lookupLiveMap(out_live_table, n);
        G_nodeList out_nodes = NULL;
        for(Temp_tempList p = n_out; p; p = p->tail){
            G_node cur = Live_lookupTempMap(m, p->head);
            if(!cur){
                cur = G_Node(live, p->head);
                Live_enter(m, p->head, cur);
            }
            out_nodes = G_NodeList(cur, out_nodes);
        }
        for(G_nodeList i = out_nodes; i; i = i->tail){
            for(G_nodeList j = i->tail; j; j = j->tail){
                G_node node1 = i->head, node2 = j->head;
                G_addEdge(node1, node2);
                G_addEdge(node2, node1);
            }
        }
        //20181225 A special case for caller saved registers. If a Temp_temp lives across a call, then it is conflict with all caller-saved registers.
        string assem = cur_instr->u.OPER.assem;
        if(assem[0] == 'c' && assem[1] == 'a' && assem[2] == 'l'){
            Temp_tempList intersect_in_out = intersect_tempList(n_in, n_out);
            G_nodeList out_nodes = NULL;
            if(intersect_in_out == NULL) continue;
            else intersect_in_out = union_tempList(intersect_in_out, F_callerSavedRegisters());
            for(Temp_tempList p = intersect_in_out; p; p = p->tail){
                G_node cur = Live_lookupTempMap(m, p->head);
                if(!cur){
                    cur = G_Node(live, p->head);
                    Live_enter(m, p->head, cur);
                }
                out_nodes = G_NodeList(cur, out_nodes);
            }
            for(G_nodeList i = out_nodes; i; i = i->tail){
                for(G_nodeList j = i->tail; j; j = j->tail){
                    G_node node1 = i->head, node2 = j->head;
                    G_addEdge(node1, node2);
                    G_addEdge(node2, node1);
                }
            }
        }
        
        
    }
    lg.graph = live;
    lg.moves = live_ml_first;
    
	return lg;
}

void Live_print(struct Live_graph lg){
    
    G_graph live = lg.graph;
    printf("Showing the live graph...\n");
    G_show(stdout, G_nodes(live), printTemp);
    printf("End showing the live graph...\n");
    
    
    printf("Showing the move list...\n");
    Live_moveList moves = lg.moves;
    for(Live_moveList p = moves; p; p = p->tail){
        printTemp((Temp_temp)G_nodeInfo(p->src));
        printTemp((Temp_temp)G_nodeInfo(p->dst));
        printf("(%d)\n",G_goesTo(p->src, p->dst));
    }
    printf("End showing the move list...\n");
    
}