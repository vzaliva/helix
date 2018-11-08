Require Import Helix.FSigmaHCOL.FSigmaHCOLEval.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Coq.Strings.String.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Program Definition FloatV64Zero := Float64V (@FF2B _ _ (F754_zero false) _).

Program Definition FloatV64One := Float64V (BofZ _ _ _ _ 1%Z).
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(* sample definition to be moved to DynWin.v *)
Definition DynWinFSHCOL: @FSHOperator Float64 (1 + 4) 1 :=
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


Inductive FSHValType {ft:FloatT}: Type :=
| FSHnatValType: FSHValType
| FSHFloatValType: FSHValType
| FSHvecValType {n:nat}: FSHValType.

Require Import Coq.Lists.List.
Import ListNotations.

Definition getIRType
           {ft: FloatT}
           (t: @FSHValType ft): typ :=
  match t with
  | FSHnatValType => TYPE_I 64%Z (* TODO: config *)
  | FSHFloatValType => match ft with
                      | Float32 => TYPE_Float
                      | Float64 => TYPE_Double
                      end
  | FSHvecValType n => match ft with
                      | Float32 => TYPE_Array (Z.of_nat n) TYPE_Float
                      | Float64 => TYPE_Array (Z.of_nat n) TYPE_Double
                      end
  end.

Definition genIRGlobals
           {ft: FloatT}:
           (list (string* (@FSHValType ft))) -> (toplevel_entities (list block))
  := List.map
       (fun g:(string* (@FSHValType ft)) =>
          let (n,t) := g in
          TLE_Global {|
             g_ident        := Name n;
             g_typ          := getIRType t ;
             g_constant     := false ;
             g_exp          := None ;
             g_linkage      := Some LINKAGE_External ;
             g_visibility   := None ;
             g_dll_storage  := None ;
             g_thread_local := None ;
             g_unnamed_addr := true ;
             g_addrspace    := None ;
             g_externally_initialized:= true ;
             g_section      := None ;
             g_align        := Some 16%Z ; (* TODO: not for all? *)
           |}
       ).

Definition LLVMGen
           {i o: nat}
           {ft: FloatT}
           (globals: list (string* (@FSHValType ft)))
           (fshcol: @FSHOperator ft i o) (funname: string)
  :option (toplevel_entities (list block))
  := Some
       (genIRGlobals globals ++
                     [TLE_Definition
                        {|
                          df_prototype   :=
                            {|
                              dc_name        := Name funname;
                              dc_type        := TYPE_Function
                                                  (getIRType (@FSHvecValType ft o))
                                                  [
                                                    TYPE_Pointer
                                                      (getIRType (@FSHvecValType ft o))
                                                  ] ;
                              dc_param_attrs := ([],[[PARAMATTR_Align 16%Z]]);
                              dc_linkage     := None;
                              dc_visibility  := None;
                              dc_dll_storage := None;
                              dc_cconv       := None;
                              dc_attrs       := [];
                              dc_section     := None;
                              dc_align       := None;
                              dc_gc          := None;
                            |} ;
                          df_args        := [Name "X"];
                          df_instrs      := [];
                        |}
                     ]
       ).


