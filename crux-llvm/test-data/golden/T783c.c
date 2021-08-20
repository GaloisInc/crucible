// Minimized from the ntdrivers/cdaudio.i.cil-2.c SV-COMP benchmark from
// https://github.com/sosy-lab/sv-benchmarks/blob/99d37c5b4072891803b9e5c154127c912477f705/c/ntdrivers/cdaudio.i.cil-2.c
#include <stdlib.h>

struct CDROM_TOC {
  unsigned char FirstTrack ;
  unsigned char LastTrack ;
  unsigned char TrackData[100] ;
};

void HpCdrProcessLastSession(struct CDROM_TOC *Toc) {
  unsigned long index ;

  index = Toc->FirstTrack;
  if (index) {
    index -= 1UL;
    Toc->FirstTrack = Toc->TrackData[0];
    Toc->LastTrack = Toc->TrackData[index];
    Toc->TrackData[0] = Toc->TrackData[index];
  } else {
    Toc->LastTrack = 0;
    Toc->FirstTrack = Toc->LastTrack;
  }
}

int main() {
  struct CDROM_TOC *Toc = malloc(sizeof(struct CDROM_TOC));
  HpCdrProcessLastSession(Toc);
  return 0;
}
