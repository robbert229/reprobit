/* Frame-objects fixture: MSVC 5.0 keeps `i` in the word of the parameter
   `down` once `down` is dead, and records `i` 4 bytes above that word.
   cl /nologo /TC /ML /Zi /O2 /Ob1 /FAs /Fahomed.asm /Fohomed.obj
      /Fdhomed.obj.pdb -c homed.c */
typedef struct Point { float x, y; } Point;
typedef struct Icon { unsigned int width, height; } Icon;
typedef struct Row { Icon *icons[8]; unsigned int count; } Row;
extern void icon_draw(Icon *icon, Point *pos);

void homed_draw(Row *row, unsigned int across, unsigned int down)
{
    Point pos;
    unsigned int x;
    unsigned int height;
    unsigned int i;

    x = 0;
    height = 0;
    pos.y = (float)down;
    across += down;
    for (i = 0; i < row->count; i++) {
        if (row->icons[i]) {
            pos.x = (float)(x + across);
            icon_draw(row->icons[i], &pos);
            if ((int)row->icons[i]->height > (int)height) height = row->icons[i]->height;
            x += row->icons[i]->width;
        }
        else {
            pos.y += height;
            height = 0;
            x = 0;
        }
    }
}
