#ifndef LIVENESS_H
#define LIVENESS_H
#include "table.h"
typedef struct Live_moveList_ *Live_moveList;
struct Live_moveList_ {
	G_node src, dst;
	Live_moveList tail;
};

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail);

struct Live_graph {
	G_graph graph;
	Live_moveList moves;
};
Temp_temp Live_gtemp(G_node n);

typedef TAB_table Live_table;
Live_table Live_getTable();
void Live_enter(Live_table, Temp_temp, void *);
G_node Live_lookupTempMap(Live_table, Temp_temp);

struct Live_graph Live_liveness(G_graph flow);
void Live_print(struct Live_graph);
#endif
