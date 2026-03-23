%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                         %%
%%  Contains types for Job Shop Scheduler                  %%
%%                                                         %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type Int_OneDim = array[Integer];

type Int_TwoDim = array[Int_Onedim];
type Int_ThreeDim = array[Int_Twodim];

type Real_OneDim = array[Real];
type Real_TwoDim = array[Real_OneDim];

type Pair = record [Pred, Succ:Integer];
type Pair_OneDim = array [Pair];


type SortRec = record [Val: Real; Loc: Integer];
type Sort_OneDim = array [SortRec];
type PreSortRec = record [Val:Real_OneDim; IRow,JRow:Int_OneDim];
type PreSortRec_OneDim = array [PreSortRec];

type SRec = record [Start, Finish, Duration: Real; Priority: Integer];
type SRec_OneDim = array [SRec];

type Element = record [Alpha, Beta: Real; Priority: Integer];
type AB_OneDim = array [Element];
type AB_TwoDim = array [AB_OneDim];
type MaxRec = record [Val, Job, Seg: Integer];
type Max_OneDim = array [MaxRec];
type Max_TwoDim = array [Max_OneDim];
type SegRec = record [EnableCnt: integer; Max: MaxRec; Priority: Integer; 
                      Fired, Leaf: Boolean];
type Seg_OneDim = array [SegRec];
type Seg_TwoDim = array [Seg_OneDim];

type ArcRec = record [Job, Seg: Integer; Max: MaxRec];
type Arc_OneDim = array [ArcRec];
type Arc_TwoDim = array [Arc_OneDim];
type Arc_ThreeDim = array [Arc_TwoDim];
