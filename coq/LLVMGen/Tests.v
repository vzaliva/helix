Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.LLVMGen.Compiler.
Require Import Helix.LLVMGen.Externals.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMEvents.
Require Import Vellvm.Denotation.
Require Import Vellvm.Handlers.Memory.
Require Import Vellvm.TopLevel.
Require Import Vellvm.LLVMAst.

Require Import ITree.ITree.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import ExtLib.Structures.Monads.

Import ListNotations.

Program Definition binary32zero : binary32 := @FF2B _ _ (F754_zero false) _.
Definition FloatV32Zero := Float32V binary32zero.

Program Definition FloatV32One := Float32V (BofZ _ _ _ _ 1%Z).
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

Section DoubleTests.
  Program Definition binary64zero : binary64 := (@FF2B _ _ (F754_zero false) _).
  Definition FloatV64Zero := Float64V binary64zero.

  Program Definition FloatV64One := Float64V (BofZ _ _ _ _ 1%Z).
  Next Obligation. reflexivity. Qed.
  Next Obligation. reflexivity. Qed.

  (* sample definition to be moved to DynWin.v *)
  Definition DynWin64_test: @FSHOperator Float64 (1 + 4) 1 :=
    FSHCompose (FSHBinOp (AZless (AVar 1) (AVar 0)))
     (FSHHTSUMUnion (APlus (AVar 1) (AVar 0))
        (FSHCompose (FSHeUnion (NConst 0) FloatV64Zero)
           (FSHIReduction 3 (APlus (AVar 1) (AVar 0)) FloatV64Zero
              (FSHCompose
                 (FSHCompose (FSHPointwise (AMult (AVar 0) (ANth 3 (VVar 3) (NVar 2))))
                    (FSHInductor (NVar 0) (AMult (AVar 1) (AVar 0)) FloatV64One))
                 (FSHeT (NConst 0)))))
        (FSHCompose (FSHeUnion (NConst 1) FloatV64Zero)
           (FSHIReduction 2 (AMax (AVar 1) (AVar 0)) FloatV64Zero
              (FSHCompose (FSHBinOp (AAbs (AMinus (AVar 1) (AVar 0))))
                 (FSHIUnion 2 (APlus (AVar 1) (AVar 0)) FloatV64Zero
                    (FSHCompose (FSHeUnion (NVar 0) FloatV64Zero)
                       (FSHeT
                          (NPlus (NPlus (NConst 1) (NMult (NVar 1) (NConst 1)))
                             (NMult (NVar 0) (NMult (NConst 2) (NConst 1))))))))))).

  Definition BinOp_less_test: @FSHOperator Float64 (2+2) 2 :=
    FSHBinOp (AZless (AVar 1) (AVar 0)).

  Definition BinOp_plus_test: @FSHOperator Float64 (2+2) 2 :=
    FSHBinOp (APlus (AVar 1) (AVar 0)).

  Definition Pointwise_plus1_test: @FSHOperator Float64 8 8 :=
    FSHPointwise (APlus (AConst FloatV64One) (AVar 0)).

  Definition Pointwise_plusD_test: @FSHOperator Float64 8 8 :=
    FSHPointwise (APlus (AVar 0) (AVar 2)).

  Definition Compose_pointwise_test: @FSHOperator Float64 8 8 :=
    FSHCompose Pointwise_plus1_test Pointwise_plus1_test.

  Record FSHCOLTest :=
    mkFSHCOLTest
      {
        ft: FloatT;
        i: nat;
        o: nat;
        name: string;
        globals: list (string * (@FSHValType ft)) ;
        op: @FSHOperator ft i o;
      }.

  Definition IReduction_test: @FSHOperator Float64 4 4 :=
    FSHIReduction 3 (APlus (AVar 1) (AVar 0)) FloatV64Zero FSHId.

  Definition IUnion_test: @FSHOperator Float64 4 4 :=
    FSHIUnion 4 (APlus (AVar 1) (AVar 0)) FloatV64Zero
              (FSHCompose
                 (FSHeUnion (NVar 0) FloatV64Zero)
                 (FSHCompose
                    FSHId
                    (FSHeT (NVar 0)))).

  Definition Inductor_test: @FSHOperator Float64 1 1 :=
    FSHInductor (NConst 8) (AMult (AVar 1) (AVar 0)) FloatV64One.

  Definition SUMUnionTest: @FSHOperator Float64 4 4 :=
    FSHHTSUMUnion (APlus (AVar 1) (AVar 0)) FSHId FSHId.


End DoubleTests.

Section SingleTests.
  (* sample definition to be moved to DynWin.v *)
  Definition DynWin32_test: @FSHOperator Float32 (1 + 4) 1 :=
    FSHCompose (FSHBinOp (AZless (AVar 1) (AVar 0)))
     (FSHHTSUMUnion (APlus (AVar 1) (AVar 0))
        (FSHCompose (FSHeUnion (NConst 0) FloatV32Zero)
           (FSHIReduction 3 (APlus (AVar 1) (AVar 0)) FloatV32Zero
              (FSHCompose
                 (FSHCompose (FSHPointwise (AMult (AVar 0) (ANth 3 (VVar 3) (NVar 2))))
                    (FSHInductor (NVar 0) (AMult (AVar 1) (AVar 0)) FloatV32One))
                 (FSHeT (NConst 0)))))
        (FSHCompose (FSHeUnion (NConst 1) FloatV32Zero)
           (FSHIReduction 2 (AMax (AVar 1) (AVar 0)) FloatV32Zero
              (FSHCompose (FSHBinOp (AAbs (AMinus (AVar 1) (AVar 0))))
                 (FSHIUnion 2 (APlus (AVar 1) (AVar 0)) FloatV32Zero
                    (FSHCompose (FSHeUnion (NVar 0) FloatV32Zero)
                       (FSHeT
                          (NPlus (NPlus (NConst 1) (NMult (NVar 1) (NConst 1)))
                             (NMult (NVar 0) (NMult (NConst 2) (NConst 1))))))))))).

End SingleTests.

Local Open Scope string_scope.

Definition all_tests :=
  [
    {| name:="dynwin64"; op:=DynWin64_test ; globals:=[("D", @FSHvecValType Float64 3)] |} ;
      {| name:="dynwin32"; op:=DynWin32_test ; globals:=[("D", @FSHvecValType Float32 3)] |} ;
      {| name:="binop_less"; op:=BinOp_less_test; globals:=[] |} ;
      {| name:="binop_plus"; op:=BinOp_plus_test; globals:=[] |} ;
      {| name:="ireduction"; op:=IReduction_test; globals:=[] |} ;
      {| name:="iunion"; op:=IUnion_test; globals:=[] |} ;
      {| name:="inductor"; op:=Inductor_test; globals:=[] |} ;
      {| name:="sumunion"; op:=SUMUnionTest; globals:=[] |} ;
      {| name:="pointwise_plus1"; op:=Pointwise_plus1_test; globals:=[] |} ;
      {| name:="pointwise_plusD"; op:=Pointwise_plusD_test; globals:=[("D", @FSHFloatValType Float64)] |} ;
      {| name:="compose_pointwise"; op:=Compose_pointwise_test ; globals:=[]|}
  ].


Import MonadNotation.

Import IO.
Export IO.DV.

(* Maybe this should go to FSHCOL.v *)
Definition floatTRunType (ft:FloatT): Type :=
  match ft with
  | Float32 => binary32
  | Float64 => binary64
  end.

Definition rotate {A:Type} (default:A) (lst:list (A)): (A*(list A))
  := match lst with
     | [] => (default,[])
     | (x::xs) => (x,app xs [x])
     end.

Definition floatVzero (ft: FloatT): FloatV ft :=
  match ft with
  | Float32 => FloatV32Zero
  | Float64 => FloatV64Zero
  end.

Fixpoint constArray
           {ft: FloatT}
           (len: nat)
           (data:list (FloatV ft))
  : ((list (FloatV ft))*(list (texp typ)))
  :=
    match len with
    | O => (data,[])
    | S len' => let '(x, data') := rotate (floatVzero ft) data in
               let '(data'',res) := constArray len' data' in
               (data'', (FloatTtyp ft, genFloatV x) :: res)
    end.

Fixpoint initIRGlobals
         {ft: FloatT}
         (data: list (FloatV ft))
         (x: list (string * (@FSHValType ft)))
  : (list (FloatV ft) * list (toplevel_entity typ (list (block typ))))
  :=
    match x with
    | nil => (data,[])
    | cons (n,t) xs =>
      let (ds,gs) := initIRGlobals data xs in
      let (ds,arr) := match t with
                      | FSHnatValType => (ds,[]) (* TODO: no supported *)
                      | FSHFloatValType => (ds,[]) (* TODO: no supported *)
                      | FSHvecValType n => constArray n ds
                      end in
      (ds, TLE_Global _ _ {|
               g_ident        := Name n;
               g_typ          := getIRType t ;
               g_constant     := true ;
               g_exp          := Some (EXP_Array _ arr);
               g_linkage      := Some LINKAGE_Internal ;
               g_visibility   := None ;
               g_dll_storage  := None ;
               g_thread_local := None ;
               g_unnamed_addr := true ;
               g_addrspace    := None ;
               g_externally_initialized := false ;
               g_section      := None ;
               g_align        := Some Utils.PtrAlignment ;
             |} :: gs)
    end.

Definition genMain
           {ft: FloatT}
           (i o: nat)
           (op_name: string)
           (globals: list (string * (@FSHValType ft)))
           (data:list (FloatV ft))
  :
    LLVMAst.toplevel_entities _ (list (LLVMAst.block typ)) :=
  let x := Name "X" in
  let xtyp := getIRType (@FSHvecValType ft i) in
  let xptyp := TYPE_Pointer xtyp in
  let '(_,xdata) := constArray i data in
  let y := Name "Y" in
  let ytyp := getIRType (@FSHvecValType ft o) in
  let yptyp := TYPE_Pointer ytyp in
  let ftyp := TYPE_Function TYPE_Void [xptyp; yptyp] in
  let z := Name "z" in
  [
    TLE_Comment _ _ " X data" ;
      TLE_Global _ _
        {|
          g_ident        := x;
          g_typ          := xtyp;
          g_constant     := true;
          g_exp          := Some (EXP_Array _ xdata);
          g_linkage      := None;
          g_visibility   := None;
          g_dll_storage  := None;
          g_thread_local := None;
          g_unnamed_addr := false;
          g_addrspace    := None;
          g_externally_initialized := false;
          g_section      := None;
          g_align        := None;
        |} ;
      TLE_Comment _ _ " Main function" ;
      TLE_Definition _ _
        {|
          df_prototype   :=
            {|
              dc_name        := Name ("main") ;
              dc_type        := TYPE_Function ytyp [] ;
              dc_param_attrs := ([],
                                 []);
              dc_linkage     := None ;
              dc_visibility  := None ;
              dc_dll_storage := None ;
              dc_cconv       := None ;
              dc_attrs       := []   ;
              dc_section     := None ;
              dc_align       := None ;
              dc_gc          := None
            |} ;
          df_args        := [];
          df_instrs      := [
                             {|
                               blk_id    := Name "main_block" ;
                               blk_phis  := [];
                               blk_code  :=
                                 List.app (@allocTempArrayCode ft y o)
                                          [
                                            (IVoid 0, INSTR_Call _ (TYPE_Void, EXP_Ident _ (ID_Global (Name op_name))) [(xptyp, EXP_Ident _ (ID_Global x)); (yptyp, EXP_Ident _ (ID_Local y))]) ;
                                              (IId z, INSTR_Load _ false ytyp (yptyp, EXP_Ident _ (ID_Local y)) None )
                                          ]
                               ;

                               blk_term  := (IId (Name "main_ret"), TERM_Ret _ (ytyp, EXP_Ident _ (ID_Local z))) ;
                               blk_comments := None
                             |}

                           ]
        |}].

Definition test_interpreter := interpreter_user helix_intrinsics.

Definition runFSHCOLTest (t:FSHCOLTest) (data:list (FloatV t.(ft)))
  :=
    match t return (list (FloatV t.(ft)) -> _) with
    | mkFSHCOLTest ft i o name globals op =>
      fun data' =>
        let (data'', ginit) := initIRGlobals data' globals in
        let ginit := app [TLE_Comment _ _ "Global variables"] ginit in
        let main := genMain i o name globals data'' in
        match LLVMGen' (m := sum string) globals false op name with
        | inl _ => (None, None)
        | inr prog =>
          let code := app (app ginit prog) main in
          (Some prog, Some (test_interpreter code))
        end
    end data.
