#include "idris_rts.h"

void blank(void* tex, int w, int h);

typedef struct {
    double x0, y0;
    double lx, ly, lc;
    double x1, y1;
} segment;

typedef struct {
    segment* d;
    int length;
    int available;
} list;

list newList();

void listPush(list l, segment s);

void listClear(list l);

void fillPolygon(void* tex, int w, int h, int minX, int maxX, int minY, int maxY, VAL idrisEdges);

void drawCircle(void* tex, int w, int h, double cx, double cy, double ri, double ro);

bool popSegment(VAL* idrisEdges, int y, segment* newSegment);

void drawRow(void* tex, int w, int h, int minX, int maxX, int y, list segments);

double horizontalIntersect(segment s, double y);
double verticalIntersect(segment s, double x);

void ink(void* tex, int w, int h, int x, int y, double covered);

int darken(uint8_t start, double covered);
