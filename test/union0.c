#ifdef CInfo
#define GatherCopyInfo 1
#endif

#ifdef FInfo
#define GatherFlopInfo 1
#endif

#define _INTRINSICS_ 1

#include "sisal.h"

extern int sisal_file_io;

int ProvideModuleDataBaseOnAllCompiles;

static void InitGlobalData();

#undef _MAIN
static void         _MAIN();	/* [Call=F,Rec=F,Par=F,Xmk=F,Mk=e] */
#undef IReadIntegerVector
static POINTER      IReadIntegerVector();
#undef IWriteIntegerVector
static void         IWriteIntegerVector();
#undef SFreeIntegerVector
static void         SFreeIntegerVector();
#undef PFreeIntegerVector
static void         PFreeIntegerVector();
#undef ReadUn13
static POINTER      ReadUn13();
#undef WriteUn13
static void         WriteUn13();
#undef IReadUn13
static POINTER      IReadUn13();
#undef IWriteUn13
static void         IWriteUn13();
#undef SFreeUn13
static void         SFreeUn13();
#undef PFreeUn13
static void         PFreeUn13();
#undef IReadDoubleVector
static POINTER      IReadDoubleVector();
#undef IWriteDoubleVector
static void         IWriteDoubleVector();
#undef SFreeDoubleVector
static void         SFreeDoubleVector();
#undef PFreeDoubleVector
static void         PFreeDoubleVector();

struct Un13 {
  union {
    int     Fld0;   float   Fld1;   POINTER Fld2;   
      } Data;
int  RefCount;    int  Tag;         LOCK_TYPE Mutex; 
    };

struct Args21 {   
struct ActRec *FirstAR; int Count;   
int     In1;    float   In2;    POINTER In3;    POINTER Out1;   
  POINTER Out2;   POINTER Out3;   
  };

struct Args25 {   
struct ActRec *FirstAR; int Count;   
POINTER In1;    char    Out1;   char    Out2;   char    Out3;   
  };

struct Args26 {   
struct ActRec *FirstAR; int Count;   
int     In1;    float   In2;    POINTER In3;    char    Out1;   
  char    Out2;   char    Out3;   
  };

static void ArrIntCopy( dest, source, num )
POINTER  dest;
POINTER  source;
register int num;
{
  register int  i;
  register int  *src = (int*) source;
  register int  *dst = (int*) dest;
/* _VECTOR_ */
/* _ASSOC_ */
/* _SAFE(dst) */
  for ( i = 0; i < num; i++ )
    dst[i] = src[i];
}

static void ArrDblCopy( dest, source, num )
POINTER  dest;
POINTER  source;
register int num;
{
  register int  i;
  register double  *src = (double*) source;
  register double  *dst = (double*) dest;
/* _VECTOR_ */
/* _ASSOC_ */
/* _SAFE(dst) */
  for ( i = 0; i < num; i++ )
    dst[i] = src[i];
}

static void _MAIN( args )
FUNCTION args;
{
  register POINTER tmp4;
  register int tmp6;
  register int tmp5;
  register int tmp9;
  register int tmp8;
  register int tmp7;

#undef  MY_LOCK
#undef  MY_UNLOCK
#define MY_LOCK(x)
#define MY_UNLOCK(x)

  UBld( tmp4, struct Un13, 1, 0 );
  ((struct Un13*)tmp4)->Data.Fld0 = ((struct Args26*)args)->In1;
  tmp5 = ((struct Un13*)tmp4)->Tag;

/* union0.sis.25: is a(union un[a:x]),is b(union un[b:y]),is d(union un[d:z]) */
  switch ( tmp5 ) {
    case 1:
    case 2:
      tmp7 = (False);
      break;
    case 0:
      tmp7 = (True);
      break;
    default:
      Error( "TagCase", "ILLEGAL UNION TAG" );
  }
  UBld( tmp4, struct Un13, 1, 1 );
  ((struct Un13*)tmp4)->Data.Fld1 = ((struct Args26*)args)->In2;
  tmp6 = ((struct Un13*)tmp4)->Tag;
  switch ( tmp6 ) {
    case 0:
    case 2:
      tmp8 = (False);
      break;
    case 1:
      tmp8 = (True);
      break;
    default:
      Error( "TagCase", "ILLEGAL UNION TAG" );
  }
  UBld( tmp4, struct Un13, 1, 2 );
  ((struct Un13*)tmp4)->Data.Fld2 = ((struct Args26*)args)->In3;
  tmp6 = ((struct Un13*)tmp4)->Tag;

/* union0.sis.26: end function */
  switch ( tmp6 ) {
    case 0:
    case 1:
      tmp9 = (False);
      break;
    case 2:
      tmp9 = (True);
      break;
    default:
      Error( "TagCase", "ILLEGAL UNION TAG" );
  }
  ((struct Args26*)args)->Out1 = tmp7;
  ((struct Args26*)args)->Out2 = tmp8;
  ((struct Args26*)args)->Out3 = tmp9;

#undef  MY_LOCK
#undef  MY_UNLOCK
#define MY_LOCK(x)    MY_LOCK_BACKUP(x)
#define MY_UNLOCK(x)  MY_UNLOCK_BACKUP(x)
}

static int *GInit = NULL;

static void InitGlobalData()
{
  SLockParent;

  if ( GInit == NULL )
    GInit = (int *) Alloc( sizeof(int) );
  else if ( *GInit ) {
    SUnlockParent;
    return;
    }

  *GInit = TRUE;


  SUnlockParent;
}

void SisalMain( args )
POINTER args;
{
#ifdef CInfo
  SaveCopyInfo;
#endif
#ifdef FInfo
  SaveFlopInfo;
#endif
  /* Set file I/O flag for output... */
  sisal_file_io = 0;
  _MAIN( args );
}

#undef GatherCopyInfo

FUNCTION ReadFibreInputs()
{
  int previous_io_state = sisal_file_io;
  register struct Args26 *args = (struct Args26*) Alloc( sizeof( struct Args26 ) );
  /* Set file I/O flag for input... */
  sisal_file_io = 0;
  ReadInt( args->In1 );
  ReadFlt( args->In2 );
  args->In3 = ReadIntegerVector();
  sisal_file_io = previous_io_state;
  return( (FUNCTION) args );
}

#ifdef CInfo
#define GatherCopyInfo 1
#endif

void WriteFibreOutputs( args )
FUNCTION args;
{
  int previous_io_state = sisal_file_io;
  register struct Args26 *p = (struct Args26*) args;
  /* Set file I/O flag for input... */
  sisal_file_io = 0;
  WriteBool( (p->Out1) );
  WriteBool( (p->Out2) );
  WriteBool( (p->Out3) );
  sisal_file_io = previous_io_state;
}
