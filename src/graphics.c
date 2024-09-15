#include "idris_rts.h"
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

void blank(void* tex, int w, int h) {
    for (int i = 0; i < w * h; i++) {
        ((int*)tex)[i] = 0xffffff;
    }
}

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

list newList() {
    list result = {
        malloc(sizeof(segment)),
        0,
        1
    };
    return result;
}

void listPush(list* l, segment s) {
    if (l->length == l->available) {
        l->available *= 2;
        l->d = realloc(l->d, l->available * sizeof(segment));
    }
    l->d[l->length] = s;
    l->length++;
}

void listClear(list* l) {
    l->length = 0;
}

double horizontalIntersect(segment s, double y) {
    return (s.lc-s.ly*y)/s.lx;
}

double verticalIntersect(segment s, double x) {
    return (s.lc-s.lx*x)/s.ly;
}

int darken(int start, double covered, int field) {
    int startChannel = (start >> field) & 0xff;
    int result = startChannel - (int) (256*covered);
    return result > 0 ? result << field : 0;
}

void ink(void* tex, int w, int h, int x, int y, double covered) {
    if (covered <= 0 || x < 0 || x >= w || y < 0 || y >= h) return;
    int i = y * w + x;
    if (covered >= 1) {
        ((int*)tex)[i] = 0;
        return;
    }
    int startColour = ((int*)tex)[i];
    if (startColour == 0) return;
    ((int*)tex)[i] = darken(startColour, covered, 16) | darken(startColour, covered, 8) | darken(startColour, covered, 0);
    //printf("Started %x, ended %x, darkened by %.2f\n", startColour, ((int*)tex)[i], covered);
}

// I could make this more efficient by sorting the list then iterating though it, but that's more complicated and probably not necessary.
void drawRow(void* tex, int w, int h, int minX, int maxX, int y, list segments) {
    //printf("Row %d, segments %d\n", y, segments.length);
    for (int i = 0; i < segments.length; i++) {
        if (segments.d[i].x0 > segments.d[i].x1) {
            double temp = segments.d[i].x0;
            segments.d[i].x0 = segments.d[i].x1;
            segments.d[i].x1 = temp;
            temp = segments.d[i].y0;
            segments.d[i].y0 = segments.d[i].y1;
            segments.d[i].y1 = temp;
        }
    }
    int cornerCovered = 0;
    for (int x = minX; x <= maxX; x++) {
        double covered = (double) cornerCovered;
        for (int i = 0; i < segments.length; i++) {
            segment s = segments.d[i];
            if (s.x0 >= x + 1 || (s.x1 < x && x >= 0)) continue;
            if (((s.x0 >= x || x < 0) && s.y0 == y) || (s.x1 < x + 1 && s.y1 == y)) {
                cornerCovered += s.lx < 0 ? 1 : -1;
            }
            if (s.x0 < x) {
                //printf("pixel=(%d,%d), initial ys=%.2f, %.2f, ", x, y, s.y0, s.y1);
                s.x0 = x;
                s.y0 = verticalIntersect(s, x);
                covered += ((double)y + 1 - s.y0) * (s.ly < 0 ? 1 : -1);
                //printf("intersect y=%.2f, covered=%.2f\n", s.y0, covered);
            }
            if (s.x1 >= x + 1) {
                s.x1 = x + 1;
                s.y1 = verticalIntersect(s, x + 1);
            }
            covered += ((double)x + 1 - (s.x0 + s.x1)/2) * fabs(s.y0 - s.y1) * (s.lx < 0 ? 1 : -1);
        }
        ink(tex, w, h, x, y, covered);
    }
}

bool popSegment(VAL* idrisEdges, int y, segment* newSegment) {
    if (CTAG(*idrisEdges) == 0) { // Empty list
        return false;
    } else { // Cons
        VAL edge = idris_getConArg(*idrisEdges, 0);
        VAL p0 = idris_getConArg(edge, 0);
        VAL l = idris_getConArg(idris_getConArg(edge, 1), 0);
        VAL p1 = idris_getConArg(idris_getConArg(edge, 1), 1);
        newSegment->x0 = GETFLOAT(idris_getConArg(p0,0));
        newSegment->y0 = GETFLOAT(idris_getConArg(idris_getConArg(p0,1),0));
        newSegment->lx = GETFLOAT(idris_getConArg(l,0));
        newSegment->ly = GETFLOAT(idris_getConArg(l,1));
        newSegment->lc = GETFLOAT(idris_getConArg(l,2));
        newSegment->x1 = GETFLOAT(idris_getConArg(p1,0));
        newSegment->y1 = GETFLOAT(idris_getConArg(idris_getConArg(p1,1),0));
        //printf("(%3.1f,%3.1f) -- %+1.3f, %+1.3f, %+3.3f -- (%3.1f,%3.1f)\n", newSegment->x0, newSegment->y0, newSegment->lx, newSegment->ly, newSegment->lc, newSegment->x1, newSegment->y1);
        
        if (newSegment->y0 <= y) {
            *idrisEdges = idris_getConArg(*idrisEdges, 1);
            return true;
        } else {
            return false;
        }
    }
}

void fillPolygon(void* tex, int w, int h, int minX, int maxX, int minY, int maxY, VAL idrisEdges) {
    /*segment s;
    while (popSegment(&idrisEdges, maxY, &s)) {
        ink(tex, w, h, s.x0, s.y0, 1);
    }*/
    list currentRow = newList();
    list nextRow = newList();
    for (int y0 = minY; y0 <= maxY; y0++) {
        segment newSegment;
        while (popSegment(&idrisEdges, y0 + 1, &newSegment)) {
            listPush(&currentRow, newSegment);
            //printf("Accepted, length=%d\n", currentRow.length);
        }
        listClear(&nextRow);
        for (int i = 0; i < currentRow.length; i++) {
            if (currentRow.d[i].y1 > y0 + 1) {
                double x = horizontalIntersect(currentRow.d[i], y0 + 1);
                segment remaining = currentRow.d[i];
                remaining.x0 = x;
                remaining.y0 = y0 + 1;
                listPush(&nextRow, remaining);
                currentRow.d[i].x1 = x;
                currentRow.d[i].y1 = y0 + 1;
            }
        }
        if (y0 >= 0) {
            drawRow(tex, w, h, minX, maxX, y0, currentRow);
        }
        list swapRow = currentRow;
        currentRow = nextRow;
        nextRow = swapRow;
    }
    free(currentRow.d);
    free(nextRow.d);
}

double psqrt(double x) {
    return x > 0 ? sqrt(x) : 0;
}

double limit(double x) {
    return x > 0.5 ? 0.5 : x < -0.5 ? -0.5 : x;
}

double circlePix(void* tex, int w, int h, int x, int y, double cx, double dcy, double ro, double ri) {
    if (x >= w) return NAN;
    double r = sqrt((x+0.5-cx)*(x+0.5-cx)+dcy*dcy);
    ink(tex, w, h, x, y, limit(ro-r) + limit(r-ri));
    return r;
}

void drawCircle(void* tex, int w, int h, double cx, double cy, double ri, double ro) {
    int y = floor(cy - ro);
    if (y < 0) y = 0;
    while ((double) y < cy + ro && y < h) {
        double yd = y + 0.5; //The centre of the pixel
        double woo = psqrt((ro+1)*(ro+1) - (cy-yd)*(cy-yd));
        double woi = psqrt((ro-1)*(ro-1) - (cy-yd)*(cy-yd));
        double wio = psqrt((ri+1)*(ri+1) - (cy-yd)*(cy-yd));
        double wii = psqrt((ri-2)*ri - (cy-yd)*(cy-yd));
        int x = floor(cx-woo-0.5);
        if (x < 0) x = 0;
        double c;
        while (circlePix(tex,w,h,x++,y,cx,yd-cy,ro,ri) > ro-0.5);
        while (x + 0.5 < cx - wio && x < w) {
            ink(tex, w, h, x, y, 1);
            x++;
        }
        while (circlePix(tex,w,h,x++,y,cx,yd-cy,ro,ri) > ri-0.5);
        if (x + 0.5 < cx + wii) x = floor(cx + wii - 0.5);
        while (circlePix(tex,w,h,x++,y,cx,yd-cy,ro,ri) < ri+0.5);
        while (x + 0.5 < cx + woi && x < w) {
            ink(tex, w, h, x, y, 1);
            x++;
        }
        while (circlePix(tex,w,h,x++,y,cx,yd-cy,ro,ri) < ro+0.5);
        
        y++;
    }
}
