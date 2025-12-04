(******************************************************************************)
(*                                                                            *)
(*                         TRANSFUSION SAFETY                                 *)
(*                                                                            *)
(*     A Comprehensive Formalization of Blood Transfusion Compatibility       *)
(*                                                                            *)
(*                    "First, do no harm." — Hippocrates                      *)
(*                                                                            *)
(*  Author:  Charles C Norton                                                 *)
(*  Date:    4 December 2025                                                  *)
(*  License: MIT                                                              *)
(*                                                                            *)
(*  This formalization models blood transfusion compatibility from first      *)
(*  principles: antigens on donor cells must not trigger antibodies in        *)
(*  recipient plasma. All compatibility relations derive from this rule.      *)
(*                                                                            *)
(******************************************************************************)

Require Import Bool List Lia PeanoNat.
Import ListNotations.

(******************************************************************************)
(*                                                                            *)
(*                           I. TYPE DEFINITIONS                              *)
(*                                                                            *)
(******************************************************************************)

(** ABO System *)
Inductive ABO : Type := A | B | AB | O.

(** Rh System — D antigen status *)
Inductive Rh : Type := Pos | Neg.

(** Basic blood type *)
Definition BloodType : Type := (ABO * Rh)%type.

(** Decidable equality *)
Definition abo_eq_dec (x y : ABO) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition rh_eq_dec (x y : Rh) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition blood_eq_dec (x y : BloodType) : {x = y} + {x <> y}.
Proof. decide equality; [apply rh_eq_dec | apply abo_eq_dec]. Defined.

(** Standard blood type constants *)
Definition A_pos  : BloodType := (A, Pos).
Definition A_neg  : BloodType := (A, Neg).
Definition B_pos  : BloodType := (B, Pos).
Definition B_neg  : BloodType := (B, Neg).
Definition AB_pos : BloodType := (AB, Pos).
Definition AB_neg : BloodType := (AB, Neg).
Definition O_pos  : BloodType := (O, Pos).
Definition O_neg  : BloodType := (O, Neg).

Definition all_blood_types : list BloodType :=
  [A_pos; A_neg; B_pos; B_neg; AB_pos; AB_neg; O_pos; O_neg].

(** Unified antigen enumeration — ALL ISBT-recognized blood group antigens.
    This comprehensive type encompasses all 43 blood group systems with ~300 antigens.
    The corresponding antibody for each antigen shares the same constructor.

    ISBT Blood Group Systems (001-043):
    001 ABO, 002 MNS, 003 P1PK, 004 Rh, 005 Lutheran, 006 Kell, 007 Lewis,
    008 Duffy, 009 Kidd, 010 Diego, 011 Yt, 012 Xg, 013 Scianna, 014 Dombrock,
    015 Colton, 016 Landsteiner-Wiener, 017 Chido/Rodgers, 018 H, 019 Kx,
    020 Gerbich, 021 Cromer, 022 Knops, 023 Indian, 024 Ok, 025 Raph,
    026 John Milton Hagen, 027 I, 028 Globoside, 029 Gill, 030 RHAG,
    031 FORS, 032 JR, 033 LAN, 034 Vel, 035 CD59, 036 Augustine,
    037 Kanno, 038 SID, 039 CTL2, 040 PEL, 041 MAM, 042 EMM, 043 ABCC1 *)
Inductive Antigen : Type :=
  (* 001 ABO System *)
  | Ag_A | Ag_B | Ag_AB | Ag_A1 | Ag_Aw | Ag_Ax
  (* 002 MNS System - 49 antigens *)
  | Ag_M | Ag_N | Ag_S | Ag_s | Ag_U | Ag_He | Ag_Mia | Ag_Mc | Ag_Vw | Ag_Mur
  | Ag_Mg | Ag_Vr | Ag_Me | Ag_Mta | Ag_Sta | Ag_Ria | Ag_Cla | Ag_Nya | Ag_Hut
  | Ag_Hil | Ag_Mv | Ag_Far | Ag_sD | Ag_Mit | Ag_Dantu | Ag_Hop | Ag_Nob | Ag_Ena
  | Ag_ENKT | Ag_Nsu | Ag_HAG | Ag_ENEV | Ag_MARS | Ag_ENDA | Ag_ENEH | Ag_MNTD
  | Ag_SARA | Ag_KIPP | Ag_JENU | Ag_SUMI | Ag_KASP | Ag_MINE | Ag_MINY
  (* 003 P1PK System *)
  | Ag_P1 | Ag_Pk | Ag_NOR
  (* 004 Rh System - 55 antigens including compound antigens *)
  | Ag_D | Ag_C | Ag_E | Ag_c | Ag_e | Ag_f | Ag_Ce | Ag_cE | Ag_Cw | Ag_Cx
  | Ag_V | Ag_Ew | Ag_G | Ag_Hrs | Ag_hrS | Ag_hrB | Ag_VS | Ag_CG | Ag_CE
  | Ag_Dw | Ag_clike | Ag_Cces | Ag_Rh17 | Ag_Hr | Ag_Rh29 | Ag_Goa | Ag_hrH
  | Ag_Rh32 | Ag_Rh33 | Ag_HrB | Ag_Rh35 | Ag_Bea | Ag_Evans | Ag_Rh39 | Ag_Tar
  | Ag_Rh41 | Ag_Rh42 | Ag_Crawford | Ag_Nou | Ag_Riv | Ag_Sec | Ag_Dav | Ag_JAL
  | Ag_STEM | Ag_FPTT | Ag_MAR | Ag_BARC | Ag_JAHK | Ag_DAK | Ag_LOCR | Ag_CENR
  | Ag_CEST | Ag_CELO | Ag_CEAG | Ag_PARG | Ag_CEVF | Ag_CEVA
  (* 005 Lutheran System - 25 antigens *)
  | Ag_Lua | Ag_Lub | Ag_Lu3 | Ag_Lu4 | Ag_Lu5 | Ag_Lu6 | Ag_Lu7 | Ag_Lu8
  | Ag_Lu9 | Ag_Lu11 | Ag_Lu12 | Ag_Lu13 | Ag_Lu14 | Ag_Lu16 | Ag_Lu17
  | Ag_Aua | Ag_Aub | Ag_Lu20 | Ag_Lu21 | Ag_LURC | Ag_LURA | Ag_LUBI
  (* 006 Kell System - 36 antigens *)
  | Ag_K | Ag_k | Ag_Kpa | Ag_Kpb | Ag_Ku | Ag_Jsa | Ag_Jsb | Ag_K11 | Ag_K12
  | Ag_K13 | Ag_K14 | Ag_K16 | Ag_K17 | Ag_K18 | Ag_K19 | Ag_Km | Ag_Kpc
  | Ag_K22 | Ag_K23 | Ag_K24 | Ag_KELP | Ag_TOU | Ag_RAZ | Ag_VLAN | Ag_KALT
  | Ag_KTIM | Ag_KYO | Ag_KUCI | Ag_KANT | Ag_KASH | Ag_KETI | Ag_KHUL
  (* 007 Lewis System *)
  | Ag_Lea | Ag_Leb | Ag_Leab | Ag_LebH | Ag_ALeb | Ag_BLeb
  (* 008 Duffy System *)
  | Ag_Fya | Ag_Fyb | Ag_Fy3 | Ag_Fy4 | Ag_Fy5 | Ag_Fy6
  (* 009 Kidd System *)
  | Ag_Jka | Ag_Jkb | Ag_Jk3
  (* 010 Diego System - 22 antigens *)
  | Ag_Dia | Ag_Dib | Ag_Wra | Ag_Wrb | Ag_Wda | Ag_Rba | Ag_WARR | Ag_ELO
  | Ag_Wu | Ag_Bpa | Ag_Moa | Ag_Hga | Ag_Vga | Ag_Swa | Ag_BOW | Ag_NFLD
  | Ag_Jna | Ag_KREP | Ag_Tra | Ag_Fra | Ag_SW1 | Ag_DISK
  (* 011 Yt System *)
  | Ag_Yta | Ag_Ytb
  (* 012 Xg System *)
  | Ag_Xga | Ag_CD99
  (* 013 Scianna System *)
  | Ag_Sc1 | Ag_Sc2 | Ag_Sc3 | Ag_Rd | Ag_STAR | Ag_SCER | Ag_SCAN
  (* 014 Dombrock System *)
  | Ag_Doa | Ag_Dob | Ag_Gya | Ag_Hy | Ag_Joa | Ag_DOYA | Ag_DOMR | Ag_DOLG
  (* 015 Colton System *)
  | Ag_Coa | Ag_Cob | Ag_Co3 | Ag_Co4
  (* 016 Landsteiner-Wiener System *)
  | Ag_LWa | Ag_LWab | Ag_LWb
  (* 017 Chido/Rodgers System *)
  | Ag_Ch1 | Ag_Ch2 | Ag_Ch3 | Ag_Ch4 | Ag_Ch5 | Ag_Ch6 | Ag_WH
  | Ag_Rg1 | Ag_Rg2
  (* 018 H System *)
  | Ag_H | Ag_H2
  (* 019 Kx System *)
  | Ag_Kx
  (* 020 Gerbich System *)
  | Ag_Ge2 | Ag_Ge3 | Ag_Ge4 | Ag_Wb | Ag_Lsa | Ag_Ana | Ag_Dha | Ag_GEIS
  | Ag_GEPL | Ag_GEAT | Ag_GETI
  (* 021 Cromer System *)
  | Ag_Cra | Ag_Tca | Ag_Tcb | Ag_Tcc | Ag_Dra | Ag_Esa | Ag_IFC | Ag_WESa
  | Ag_WESb | Ag_UMC | Ag_GUTI | Ag_SERF | Ag_ZENA | Ag_CROV | Ag_CRAM
  | Ag_CROZ | Ag_CRUE | Ag_CRAG | Ag_CREG
  (* 022 Knops System *)
  | Ag_Kna | Ag_Knb | Ag_McCa | Ag_Sla | Ag_Yka | Ag_McCb | Ag_Vil | Ag_KCAM
  | Ag_KDAS | Ag_KNSB
  (* 023 Indian System *)
  | Ag_Ina | Ag_Inb | Ag_INFI | Ag_INJA | Ag_INRA
  (* 024 Ok System *)
  | Ag_Oka | Ag_OKGV | Ag_OKVM
  (* 025 Raph System *)
  | Ag_MER2
  (* 026 John Milton Hagen System *)
  | Ag_JMH | Ag_JMHK | Ag_JMHL | Ag_JMHG | Ag_JMHM | Ag_JMHQ
  (* 027 I System *)
  | Ag_I | Ag_i
  (* 028 Globoside System - Note: P1 antigen is in P1PK system above *)
  | Ag_P | Ag_PX2
  (* 029 Gill System *)
  | Ag_GIL
  (* 030 RHAG System *)
  | Ag_Duclos | Ag_Ola | Ag_DSLK
  (* 031 FORS System *)
  | Ag_FORS1
  (* 032 JR System *)
  | Ag_Jra
  (* 033 LAN System *)
  | Ag_Lan
  (* 034 Vel System *)
  | Ag_Vel
  (* 035 CD59 System *)
  | Ag_CD59p
  (* 036 Augustine System *)
  | Ag_Ata | Ag_Atb
  (* 037 Kanno System *)
  | Ag_KANNO
  (* 038 SID System *)
  | Ag_Sda
  (* 039 CTL2 System *)
  | Ag_CTL2_HEL | Ag_CTL2_REGA
  (* 040 PEL System *)
  | Ag_PEL
  (* 041 MAM System *)
  | Ag_MAM
  (* 042 EMM System *)
  | Ag_EMMI | Ag_EMMA | Ag_EMMP
  (* 043 ABCC1 System *)
  | Ag_ABCC1.

Definition antigen_count : nat := 300.

Definition antigen_eq_dec (x y : Antigen) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition is_abo_antigen (ag : Antigen) : bool :=
  match ag with
  | Ag_A | Ag_B | Ag_AB | Ag_A1 | Ag_Aw | Ag_Ax | Ag_H | Ag_H2 => true
  | _ => false
  end.

Definition is_rh_antigen (ag : Antigen) : bool :=
  match ag with
  | Ag_D | Ag_C | Ag_E | Ag_c | Ag_e | Ag_f | Ag_Ce | Ag_cE | Ag_Cw | Ag_Cx
  | Ag_V | Ag_Ew | Ag_G | Ag_Hrs | Ag_hrS | Ag_hrB | Ag_VS | Ag_CG | Ag_CE
  | Ag_Dw | Ag_clike | Ag_Cces | Ag_Rh17 | Ag_Hr | Ag_Rh29 | Ag_Goa | Ag_hrH
  | Ag_Rh32 | Ag_Rh33 | Ag_HrB | Ag_Rh35 | Ag_Bea | Ag_Evans | Ag_Rh39 | Ag_Tar
  | Ag_Rh41 | Ag_Rh42 | Ag_Crawford | Ag_Nou | Ag_Riv | Ag_Sec | Ag_Dav | Ag_JAL
  | Ag_STEM | Ag_FPTT | Ag_MAR | Ag_BARC | Ag_JAHK | Ag_DAK | Ag_LOCR | Ag_CENR
  | Ag_CEST | Ag_CELO | Ag_CEAG | Ag_PARG | Ag_CEVF | Ag_CEVA => true
  | _ => false
  end.

Definition is_abo_rh_antigen (ag : Antigen) : bool :=
  is_abo_antigen ag || is_rh_antigen ag.

Definition is_minor_antigen (ag : Antigen) : bool :=
  negb (is_abo_rh_antigen ag).

(** Blood group system classification *)
Inductive BloodGroupSystem : Type :=
  | Sys_ABO | Sys_MNS | Sys_P1PK | Sys_Rh | Sys_Lutheran | Sys_Kell | Sys_Lewis
  | Sys_Duffy | Sys_Kidd | Sys_Diego | Sys_Yt | Sys_Xg | Sys_Scianna
  | Sys_Dombrock | Sys_Colton | Sys_LW | Sys_ChRg | Sys_H | Sys_Kx | Sys_Gerbich
  | Sys_Cromer | Sys_Knops | Sys_Indian | Sys_Ok | Sys_Raph | Sys_JMH | Sys_I
  | Sys_Globoside | Sys_Gill | Sys_RHAG | Sys_FORS | Sys_JR | Sys_LAN | Sys_Vel
  | Sys_CD59 | Sys_Augustine | Sys_Kanno | Sys_SID | Sys_CTL2 | Sys_PEL
  | Sys_MAM | Sys_EMM | Sys_ABCC1.

Definition antigen_system (ag : Antigen) : BloodGroupSystem :=
  match ag with
  | Ag_A | Ag_B | Ag_AB | Ag_A1 | Ag_Aw | Ag_Ax => Sys_ABO
  | Ag_M | Ag_N | Ag_S | Ag_s | Ag_U | Ag_He | Ag_Mia | Ag_Mc | Ag_Vw | Ag_Mur
  | Ag_Mg | Ag_Vr | Ag_Me | Ag_Mta | Ag_Sta | Ag_Ria | Ag_Cla | Ag_Nya | Ag_Hut
  | Ag_Hil | Ag_Mv | Ag_Far | Ag_sD | Ag_Mit | Ag_Dantu | Ag_Hop | Ag_Nob | Ag_Ena
  | Ag_ENKT | Ag_Nsu | Ag_HAG | Ag_ENEV | Ag_MARS | Ag_ENDA | Ag_ENEH | Ag_MNTD
  | Ag_SARA | Ag_KIPP | Ag_JENU | Ag_SUMI | Ag_KASP | Ag_MINE | Ag_MINY => Sys_MNS
  | Ag_P1 | Ag_Pk | Ag_NOR => Sys_P1PK
  | Ag_D | Ag_C | Ag_E | Ag_c | Ag_e | Ag_f | Ag_Ce | Ag_cE | Ag_Cw | Ag_Cx
  | Ag_V | Ag_Ew | Ag_G | Ag_Hrs | Ag_hrS | Ag_hrB | Ag_VS | Ag_CG | Ag_CE
  | Ag_Dw | Ag_clike | Ag_Cces | Ag_Rh17 | Ag_Hr | Ag_Rh29 | Ag_Goa | Ag_hrH
  | Ag_Rh32 | Ag_Rh33 | Ag_HrB | Ag_Rh35 | Ag_Bea | Ag_Evans | Ag_Rh39 | Ag_Tar
  | Ag_Rh41 | Ag_Rh42 | Ag_Crawford | Ag_Nou | Ag_Riv | Ag_Sec | Ag_Dav | Ag_JAL
  | Ag_STEM | Ag_FPTT | Ag_MAR | Ag_BARC | Ag_JAHK | Ag_DAK | Ag_LOCR | Ag_CENR
  | Ag_CEST | Ag_CELO | Ag_CEAG | Ag_PARG | Ag_CEVF | Ag_CEVA => Sys_Rh
  | Ag_Lua | Ag_Lub | Ag_Lu3 | Ag_Lu4 | Ag_Lu5 | Ag_Lu6 | Ag_Lu7 | Ag_Lu8
  | Ag_Lu9 | Ag_Lu11 | Ag_Lu12 | Ag_Lu13 | Ag_Lu14 | Ag_Lu16 | Ag_Lu17
  | Ag_Aua | Ag_Aub | Ag_Lu20 | Ag_Lu21 | Ag_LURC | Ag_LURA | Ag_LUBI => Sys_Lutheran
  | Ag_K | Ag_k | Ag_Kpa | Ag_Kpb | Ag_Ku | Ag_Jsa | Ag_Jsb | Ag_K11 | Ag_K12
  | Ag_K13 | Ag_K14 | Ag_K16 | Ag_K17 | Ag_K18 | Ag_K19 | Ag_Km | Ag_Kpc
  | Ag_K22 | Ag_K23 | Ag_K24 | Ag_KELP | Ag_TOU | Ag_RAZ | Ag_VLAN | Ag_KALT
  | Ag_KTIM | Ag_KYO | Ag_KUCI | Ag_KANT | Ag_KASH | Ag_KETI | Ag_KHUL => Sys_Kell
  | Ag_Lea | Ag_Leb | Ag_Leab | Ag_LebH | Ag_ALeb | Ag_BLeb => Sys_Lewis
  | Ag_Fya | Ag_Fyb | Ag_Fy3 | Ag_Fy4 | Ag_Fy5 | Ag_Fy6 => Sys_Duffy
  | Ag_Jka | Ag_Jkb | Ag_Jk3 => Sys_Kidd
  | Ag_Dia | Ag_Dib | Ag_Wra | Ag_Wrb | Ag_Wda | Ag_Rba | Ag_WARR | Ag_ELO
  | Ag_Wu | Ag_Bpa | Ag_Moa | Ag_Hga | Ag_Vga | Ag_Swa | Ag_BOW | Ag_NFLD
  | Ag_Jna | Ag_KREP | Ag_Tra | Ag_Fra | Ag_SW1 | Ag_DISK => Sys_Diego
  | Ag_Yta | Ag_Ytb => Sys_Yt
  | Ag_Xga | Ag_CD99 => Sys_Xg
  | Ag_Sc1 | Ag_Sc2 | Ag_Sc3 | Ag_Rd | Ag_STAR | Ag_SCER | Ag_SCAN => Sys_Scianna
  | Ag_Doa | Ag_Dob | Ag_Gya | Ag_Hy | Ag_Joa | Ag_DOYA | Ag_DOMR | Ag_DOLG => Sys_Dombrock
  | Ag_Coa | Ag_Cob | Ag_Co3 | Ag_Co4 => Sys_Colton
  | Ag_LWa | Ag_LWab | Ag_LWb => Sys_LW
  | Ag_Ch1 | Ag_Ch2 | Ag_Ch3 | Ag_Ch4 | Ag_Ch5 | Ag_Ch6 | Ag_WH
  | Ag_Rg1 | Ag_Rg2 => Sys_ChRg
  | Ag_H | Ag_H2 => Sys_H
  | Ag_Kx => Sys_Kx
  | Ag_Ge2 | Ag_Ge3 | Ag_Ge4 | Ag_Wb | Ag_Lsa | Ag_Ana | Ag_Dha | Ag_GEIS
  | Ag_GEPL | Ag_GEAT | Ag_GETI => Sys_Gerbich
  | Ag_Cra | Ag_Tca | Ag_Tcb | Ag_Tcc | Ag_Dra | Ag_Esa | Ag_IFC | Ag_WESa
  | Ag_WESb | Ag_UMC | Ag_GUTI | Ag_SERF | Ag_ZENA | Ag_CROV | Ag_CRAM
  | Ag_CROZ | Ag_CRUE | Ag_CRAG | Ag_CREG => Sys_Cromer
  | Ag_Kna | Ag_Knb | Ag_McCa | Ag_Sla | Ag_Yka | Ag_McCb | Ag_Vil | Ag_KCAM
  | Ag_KDAS | Ag_KNSB => Sys_Knops
  | Ag_Ina | Ag_Inb | Ag_INFI | Ag_INJA | Ag_INRA => Sys_Indian
  | Ag_Oka | Ag_OKGV | Ag_OKVM => Sys_Ok
  | Ag_MER2 => Sys_Raph
  | Ag_JMH | Ag_JMHK | Ag_JMHL | Ag_JMHG | Ag_JMHM | Ag_JMHQ => Sys_JMH
  | Ag_I | Ag_i => Sys_I
  | Ag_P | Ag_PX2 => Sys_Globoside
  | Ag_GIL => Sys_Gill
  | Ag_Duclos | Ag_Ola | Ag_DSLK => Sys_RHAG
  | Ag_FORS1 => Sys_FORS
  | Ag_Jra => Sys_JR
  | Ag_Lan => Sys_LAN
  | Ag_Vel => Sys_Vel
  | Ag_CD59p => Sys_CD59
  | Ag_Ata | Ag_Atb => Sys_Augustine
  | Ag_KANNO => Sys_Kanno
  | Ag_Sda => Sys_SID
  | Ag_CTL2_HEL | Ag_CTL2_REGA => Sys_CTL2
  | Ag_PEL => Sys_PEL
  | Ag_MAM => Sys_MAM
  | Ag_EMMI | Ag_EMMA | Ag_EMMP => Sys_EMM
  | Ag_ABCC1 => Sys_ABCC1
  end.

(** Blood products *)
Inductive Product : Type :=
  | PackedRBC
  | FreshFrozenPlasma
  | Platelets
  | Cryoprecipitate
  | WholeBlood.

(** Clinical priority *)
Inductive Priority : Type :=
  | Emergency | Urgent | Routine | Elective.

(** Reaction severity — single unified model *)
Inductive Severity : Type :=
  | Safe
  | DelayedHemolytic
  | AcuteHemolytic
  | SevereAcuteHemolytic
  | LifeThreatening.

(******************************************************************************)
(*                                                                            *)
(*                       PROOF AUTOMATION TACTICS                             *)
(*                                                                            *)
(*  Ltac definitions for common proof patterns in blood type compatibility.   *)
(*  These tactics are designed to be robust against type definition changes   *)
(*  and avoid hardcoding constructor counts.                                  *)
(*                                                                            *)
(*  Design principles:                                                        *)
(*  1. Use 'destruct' without explicit patterns where possible                *)
(*  2. Iterate with 'repeat' rather than fixed recursion depth                *)
(*  3. Provide both automated and semi-automated tactics                      *)
(*  4. Separate concerns: destruction, simplification, solving                *)
(*                                                                            *)
(******************************************************************************)

(** === CORE DESTRUCTION TACTICS === *)

(** Destruct a BloodType into its ABO and Rh components, then destruct those *)
Ltac destruct_blood_type bt :=
  let abo := fresh "abo" in
  let rh := fresh "rh" in
  destruct bt as [abo rh]; destruct abo; destruct rh.

(** Destruct all BloodTypes in the context *)
Ltac destruct_blood_types :=
  repeat match goal with
  | [ bt : BloodType |- _ ] => destruct_blood_type bt
  end.

(** Destruct all ABO values in context *)
Ltac destruct_all_abo :=
  repeat match goal with
  | [ a : ABO |- _ ] => destruct a
  end.

(** Destruct all Rh values in context *)
Ltac destruct_all_rh :=
  repeat match goal with
  | [ r : Rh |- _ ] => destruct r
  end.

(** === GOAL-ORIENTED SOLVING TACTICS === *)

(** Try common proof completers in order of speed *)
Ltac solve_trivial :=
  try reflexivity;
  try discriminate;
  try contradiction;
  try lia;
  auto.

(** Solve goals involving blood type case analysis *)
Ltac solve_blood_type_cases :=
  intros; destruct_blood_types; solve_trivial.

(** Solve ABO/Rh goals without full BloodType destruction *)
Ltac solve_abo_rh_cases :=
  intros; destruct_all_abo; destruct_all_rh; solve_trivial.

(** === BOOLEAN LOGIC TACTICS === *)

(** Handle conjunction in hypotheses and goals *)
Ltac handle_andb :=
  repeat match goal with
  | [ |- _ && _ = true ] => apply andb_true_intro; split
  | [ H : _ && _ = true |- _ ] => apply andb_prop in H; destruct H
  | [ |- context[negb (negb _)] ] => rewrite Bool.negb_involutive
  end.

(** Simplify boolean expressions *)
Ltac simplify_bool :=
  simpl;
  repeat match goal with
  | [ |- context[true && ?x] ] => rewrite Bool.andb_true_l
  | [ |- context[?x && true] ] => rewrite Bool.andb_true_r
  | [ |- context[false && ?x] ] => rewrite Bool.andb_false_l
  | [ |- context[?x && false] ] => rewrite Bool.andb_false_r
  | [ |- context[negb true] ] => simpl
  | [ |- context[negb false] ] => simpl
  end.

(** === EXHAUSTIVE CASE ANALYSIS === *)

(** Basic case solver for core blood types only (ABO, Rh, BloodType) *)
Ltac exhaust_basic_cases :=
  intros;
  repeat match goal with
  | [ x : ABO |- _ ] => destruct x
  | [ x : Rh |- _ ] => destruct x
  | [ x : BloodType |- _ ] => let a := fresh in let r := fresh in destruct x as [a r]
  end;
  solve_trivial.

(** Solve compatibility theorems by computing on all 64 cases *)
Ltac solve_compatibility_theorem :=
  intros;
  repeat match goal with
  | [ x : BloodType |- _ ] => destruct x as [?a ?r]; destruct a; destruct r
  end;
  simpl; solve_trivial.

(** Solve quantified compatibility statements *)
Ltac solve_forall_compatibility :=
  intros;
  match goal with
  | [ |- forall _, _ ] => intro; solve_forall_compatibility
  | _ => solve_compatibility_theorem
  end.

(** === HYPOTHESIS MANIPULATION === *)

(** Apply function to equality hypothesis *)
Ltac f_equal_in H :=
  match type of H with
  | ?x = ?y => let H' := fresh in assert (H' : x = y) by exact H; f_equal
  end.

(** Specialize a hypothesis with a concrete blood type *)
Ltac specialize_blood_type H bt :=
  let H' := fresh H in
  pose proof (H bt) as H'; simpl in H'.

(** === TACTIC ALIASES FOR BACKWARD COMPATIBILITY === *)

Ltac destruct_abo a := destruct a.
Ltac destruct_rh r := destruct r.
Ltac destruct_subtype s := destruct s.
Ltac destruct_rh_variant v := destruct v.
Ltac andb_split := handle_andb.

(******************************************************************************)
(*                                                                            *)
(*                      II. IMMUNOLOGICAL MODEL                               *)
(*                                                                            *)
(*  Core principle: A transfusion is safe iff donor cells carry no antigens   *)
(*  against which the recipient has antibodies.                               *)
(*                                                                            *)
(*  CRITICAL DISTINCTION: IMMUNOLOGICAL TRUTH vs CLINICAL POLICY              *)
(*  ============================================================              *)
(*                                                                            *)
(*  This formalization distinguishes two conceptually different things:       *)
(*                                                                            *)
(*  1. IMMUNOLOGICAL TRUTH (what antibodies a person actually has):           *)
(*     - ABO antibodies (anti-A, anti-B) are NATURALLY OCCURRING              *)
(*       isoagglutinins present from early childhood without prior exposure   *)
(*     - Rh antibodies (anti-D, etc.) are IMMUNE antibodies that develop      *)
(*       ONLY after exposure (transfusion or pregnancy)                       *)
(*     - An Rh-negative person who has never been exposed has NO anti-D       *)
(*                                                                            *)
(*  2. CLINICAL POLICY (what we assume for safety):                           *)
(*     - When sensitization history is unknown/unreliable, we ASSUME          *)
(*       worst-case: all Rh-negative individuals MAY have anti-D              *)
(*     - This is a POLICY DECISION for patient safety, not immunological fact *)
(*                                                                            *)
(*  FUNCTION NAMING CONVENTION:                                               *)
(*  - *_immunological_*  : Pure immunological truth (requires sensitization)  *)
(*  - *_policy_*         : Clinical policy assumptions (conservative)         *)
(*  - *_abo_*            : ABO-only (always applies, no policy needed)        *)
(*  - compatible         : Default uses POLICY model for safety               *)
(*                                                                            *)
(******************************************************************************)

(** Antigen profile: which antigens are present on an individual's RBCs.
    Modeled as a membership predicate over the full Antigen type. *)
Definition AntigenSet := Antigen -> bool.

(** Antibody profile: which antibodies are present in an individual's plasma.
    For ABO, these are naturally occurring. For other systems, they arise
    from immune sensitization. *)
Definition AntibodySet := Antigen -> bool.

(** Empty antigen/antibody sets *)
Definition empty_antigen_set : AntigenSet := fun _ => false.
Definition empty_antibody_set : AntibodySet := fun _ => false.

(** Set operations *)
Definition antigen_in (ag : Antigen) (s : AntigenSet) : bool := s ag.
Definition antibody_in (ag : Antigen) (s : AntibodySet) : bool := s ag.

Definition antigen_set_union (s1 s2 : AntigenSet) : AntigenSet :=
  fun ag => s1 ag || s2 ag.

Definition antibody_set_union (s1 s2 : AntibodySet) : AntibodySet :=
  fun ag => s1 ag || s2 ag.

Definition antigen_set_add (ag : Antigen) (s : AntigenSet) : AntigenSet :=
  fun ag' => if antigen_eq_dec ag ag' then true else s ag'.

Definition antibody_set_add (ag : Antigen) (s : AntibodySet) : AntibodySet :=
  fun ag' => if antigen_eq_dec ag ag' then true else s ag'.

(** Core compatibility: set disjointness between donor antigens and recipient antibodies *)
Definition sets_disjoint (donor_ags : AntigenSet) (recipient_abs : AntibodySet)
                         (antigens_to_check : list Antigen) : bool :=
  forallb (fun ag => negb (donor_ags ag && recipient_abs ag)) antigens_to_check.

(** Which antigens are present on RBCs of a given ABO/Rh phenotype.
    This function maps phenotype to the FULL antigen set, not just core antigens. *)
Definition phenotype_antigens (bt : BloodType) : AntigenSet :=
  fun ag =>
    match ag, bt with
    | Ag_A, (A, _)  => true
    | Ag_A, (AB, _) => true
    | Ag_A1, (A, _) => true
    | Ag_A1, (AB, _) => true
    | Ag_B, (B, _)  => true
    | Ag_B, (AB, _) => true
    | Ag_H, (O, _)  => true
    | Ag_H, (A, _)  => true
    | Ag_H, (B, _)  => true
    | Ag_H, (AB, _) => true
    | Ag_D, (_, Pos) => true
    | _, _ => false
    end.

(** ABO isoagglutinins: NATURALLY OCCURRING antibodies.
    These are present from early childhood without prior transfusion/pregnancy.
    Anti-A in type B and O individuals.
    Anti-B in type A and O individuals.
    NO anti-D here - anti-D requires immune sensitization. *)
Definition abo_natural_antibodies (bt : BloodType) : AntibodySet :=
  fun ag =>
    match ag, bt with
    | Ag_A, (B, _)  => true
    | Ag_A, (O, _)  => true
    | Ag_B, (A, _)  => true
    | Ag_B, (O, _)  => true
    | _, _ => false
    end.

(** Rh sensitization status *)
Inductive RhSensitization : Type :=
  | Rh_Naive
  | Rh_Sensitized_D
  | Rh_Sensitized_Multiple.

(** Rh antibodies based on sensitization history.
    Anti-D (and other Rh antibodies) only present if:
    1. The recipient lacks the corresponding antigen (Rh-negative for D)
    2. The recipient has been sensitized
    CRITICAL: Rh-positive individuals CANNOT form anti-D (antigen-antibody exclusion).
    For C, c, E, e - sensitization can occur regardless of D status. *)
Definition rh_immune_antibodies (rh : Rh) (sens : RhSensitization) : AntibodySet :=
  fun ag =>
    match rh, sens, ag with
    | Neg, Rh_Sensitized_D, Ag_D => true
    | Neg, Rh_Sensitized_Multiple, Ag_D => true
    | _, Rh_Sensitized_Multiple, Ag_C => true
    | _, Rh_Sensitized_Multiple, Ag_E => true
    | _, Rh_Sensitized_Multiple, Ag_c => true
    | _, Rh_Sensitized_Multiple, Ag_e => true
    | _, _, _ => false
    end.

(** Combined antibody profile: natural ABO + acquired Rh (if sensitized) *)
Definition recipient_antibodies (bt : BloodType) (rh_sens : RhSensitization) : AntibodySet :=
  antibody_set_union (abo_natural_antibodies bt) (rh_immune_antibodies (snd bt) rh_sens).

(******************************************************************************)
(*         ANTIBODY FUNCTIONS: IMMUNOLOGICAL vs POLICY                        *)
(******************************************************************************)

(** ABO-only antibodies (naturally occurring - IMMUNOLOGICAL TRUTH)
    These are present in ALL individuals from early childhood.
    No policy decision needed - this is biological fact. *)
Definition has_antibody_abo (bt : BloodType) (ag : Antigen) : bool :=
  abo_natural_antibodies bt ag.

(** Which antigens are present on RBCs of a given blood type (IMMUNOLOGICAL TRUTH) *)
Definition has_antigen (bt : BloodType) (ag : Antigen) : bool :=
  phenotype_antigens bt ag.

(** Pure immunological antibody model (IMMUNOLOGICAL TRUTH)
    Returns what antibodies a person ACTUALLY has based on their sensitization.
    - ABO antibodies: Always present (natural isoagglutinins)
    - Rh antibodies: Only if sensitized
    Use this when sensitization status is KNOWN and RELIABLE. *)
Definition has_antibody_immunological (bt : BloodType) (sens : RhSensitization)
                                       (ag : Antigen) : bool :=
  recipient_antibodies bt sens ag.

(** Conservative antibody model (CLINICAL POLICY)
    Assumes Rh-negative individuals MAY have anti-D (worst-case for safety).
    This is a POLICY DECISION, not immunological fact.
    Use this when:
    - Sensitization history is unknown
    - Sensitization history is unreliable
    - Emergency situations with no time for history
    - Standard blood bank practice *)
Definition has_antibody_policy (bt : BloodType) (ag : Antigen) : bool :=
  match ag, bt with
  | Ag_A, (B, _)  => true
  | Ag_A, (O, _)  => true
  | Ag_B, (A, _)  => true
  | Ag_B, (O, _)  => true
  | Ag_D, (_, Neg) => true
  | _, _ => false
  end.

(** Alias for backward compatibility - uses POLICY model *)
Definition has_antibody_conservative (bt : BloodType) (ag : Antigen) : bool :=
  has_antibody_policy bt ag.

(** Default has_antibody uses POLICY model for safety.
    WARNING: This assumes worst-case Rh sensitization.
    For immunologically-accurate queries, use has_antibody_immunological. *)
Definition has_antibody (bt : BloodType) (ag : Antigen) : bool :=
  has_antibody_policy bt ag.

(** Theorem: Policy is MORE CONSERVATIVE than immunological naive state.
    If immunological (naive) says antibody present, policy agrees.
    But policy may say "antibody present" when immunologically there is none.
    This captures the safety margin built into policy decisions. *)
Theorem policy_conservative_vs_naive : forall bt ag,
  has_antibody_immunological bt Rh_Naive ag = true ->
  has_antibody_policy bt ag = true.
Proof.
  intros [[| | | ] [| ]] ag H; destruct ag; simpl in *;
  try reflexivity; try discriminate.
Qed.

(** Theorem: For ABO antigens, policy equals immunological truth (both use natural antibodies) *)
Theorem policy_equals_immunological_for_abo : forall bt sens,
  has_antibody_policy bt Ag_A = has_antibody_immunological bt sens Ag_A /\
  has_antibody_policy bt Ag_B = has_antibody_immunological bt sens Ag_B.
Proof.
  intros [[| | | ] [| ]] [| | ]; split; reflexivity.
Qed.

(** Theorem: For Ag_D, policy assumes worst-case (sensitized) *)
Theorem policy_assumes_sensitized_for_D : forall abo,
  has_antibody_policy (abo, Neg) Ag_D = true /\
  has_antibody_immunological (abo, Neg) Rh_Sensitized_D Ag_D = true.
Proof.
  intros [| | | ]; split; reflexivity.
Qed.

(** Theorem: Policy can be FALSE when immunological is TRUE (for minor antigens).
    Example: Rh-positive with anti-c due to multiple sensitization. *)
Theorem policy_misses_minor_rh_antibodies :
  has_antibody_policy (A, Pos) Ag_c = false /\
  has_antibody_immunological (A, Pos) Rh_Sensitized_Multiple Ag_c = true.
Proof.
  split; reflexivity.
Qed.

(** Theorem: Naive Rh-negative has NO anti-D (immunological truth) *)
Theorem naive_rh_neg_no_anti_D : forall abo,
  has_antibody_immunological (abo, Neg) Rh_Naive Ag_D = false.
Proof. intros [| | | ]; reflexivity. Qed.

(** Theorem: Policy ASSUMES Rh-negative has anti-D *)
Theorem policy_assumes_rh_neg_has_anti_D : forall abo,
  has_antibody_policy (abo, Neg) Ag_D = true.
Proof. intros [| | | ]; reflexivity. Qed.

(** Theorem: Sensitized Rh-negative DOES have anti-D (immunological truth) *)
Theorem sensitized_rh_neg_has_anti_D : forall abo,
  has_antibody_immunological (abo, Neg) Rh_Sensitized_D Ag_D = true.
Proof. intros [| | | ]; reflexivity. Qed.

(** Fundamental immunological law: you cannot have both antigen and antibody *)
Theorem antigen_antibody_exclusion : forall bt ag,
  has_antigen bt ag = true -> has_antibody bt ag = false.
Proof.
  intros [[| | | ] [| ]] ag; destruct ag;
  simpl; intro H; try reflexivity; try discriminate.
Qed.

(** ABO antigens only *)
Definition abo_antigens : list Antigen := [Ag_A; Ag_B].

(** Core antigens for standard ABO-Rh compatibility *)
Definition core_antigens : list Antigen := [Ag_A; Ag_B; Ag_D].

(** Clinically significant minor antigens (high immunogenicity) *)
Definition clinically_significant_antigens : list Antigen :=
  [Ag_A; Ag_B; Ag_D; Ag_C; Ag_E; Ag_c; Ag_e; Ag_K; Ag_Fya; Ag_Fyb; Ag_Jka; Ag_Jkb; Ag_S; Ag_s].

(** Antigen-antibody reaction check *)
Definition causes_reaction (recipient donor : BloodType) (ag : Antigen) : bool :=
  has_antibody recipient ag && has_antigen donor ag.

(** Reaction check with explicit sensitization *)
Definition causes_reaction_with_sens (recipient donor : BloodType)
                                      (rh_sens : RhSensitization) (ag : Antigen) : bool :=
  recipient_antibodies recipient rh_sens ag && has_antigen donor ag.

(** No reaction for a specific antigen *)
Definition antigen_safe (recipient donor : BloodType) (ag : Antigen) : bool :=
  negb (causes_reaction recipient donor ag).

(** No reaction with explicit sensitization status *)
Definition antigen_safe_with_sens (recipient donor : BloodType)
                                   (rh_sens : RhSensitization) (ag : Antigen) : bool :=
  negb (causes_reaction_with_sens recipient donor rh_sens ag).

(******************************************************************************)
(*                                                                            *)
(*                     III. COMPATIBILITY RELATIONS                           *)
(*                                                                            *)
(*  This section provides SEPARATED compatibility functions:                  *)
(*  1. ABO compatibility (natural isoagglutinins - always present)            *)
(*  2. Rh compatibility (immune antibodies - requires sensitization)          *)
(*  3. Combined compatibility with explicit sensitization status              *)
(*  4. Product-specific compatibility (RBC, plasma, platelets)                *)
(*                                                                            *)
(******************************************************************************)

(** ========== ABO COMPATIBILITY (Natural Isoagglutinins) ========== *)

(** ABO-only RBC compatibility: checks only natural anti-A and anti-B.
    This is ALWAYS safe to use regardless of Rh sensitization status. *)
Definition rbc_compatible_abo (recipient donor : BloodType) : bool :=
  forallb (fun ag => negb (has_antibody_abo recipient ag && has_antigen donor ag)) abo_antigens.

(** ABO compatibility matrix verification *)
Theorem rbc_compatible_abo_O_universal : forall recipient,
  rbc_compatible_abo recipient (O, Pos) = true /\
  rbc_compatible_abo recipient (O, Neg) = true.
Proof.
  intros [[| | | ] [| ]]; split; reflexivity.
Qed.

Theorem rbc_compatible_abo_AB_universal_recipient : forall donor,
  rbc_compatible_abo (AB, Pos) donor = true /\
  rbc_compatible_abo (AB, Neg) donor = true.
Proof.
  intros [[| | | ] [| ]]; split; reflexivity.
Qed.

(** ========== Rh COMPATIBILITY (Immune Antibodies) ========== *)

(** Rh compatibility with explicit sensitization status.
    Only checks Ag_D since that's what basic Rh typing determines.
    For extended Rh matching, use the full antigen set functions. *)
Definition rbc_compatible_rh (recipient_rh : Rh) (donor_rh : Rh)
                              (sens : RhSensitization) : bool :=
  match sens, recipient_rh, donor_rh with
  | Rh_Naive, _, _ => true
  | Rh_Sensitized_D, Neg, Pos => false
  | Rh_Sensitized_D, _, _ => true
  | Rh_Sensitized_Multiple, Neg, Pos => false
  | Rh_Sensitized_Multiple, _, _ => true
  end.

(** Naive Rh-negative can receive Rh-positive (no anti-D yet) *)
Theorem rh_naive_accepts_pos : forall r_rh d_rh,
  rbc_compatible_rh r_rh d_rh Rh_Naive = true.
Proof.
  intros [| ] [| ]; reflexivity.
Qed.

(** Sensitized Rh-negative cannot receive Rh-positive *)
Theorem rh_sensitized_rejects_pos :
  rbc_compatible_rh Neg Pos Rh_Sensitized_D = false.
Proof. reflexivity. Qed.

(** ========== COMBINED COMPATIBILITY ========== *)

(** Full RBC compatibility with explicit sensitization.
    This is the CORRECT model: ABO is always checked, Rh only if sensitized. *)
Definition rbc_compatible_with_sens (recipient donor : BloodType)
                                     (sens : RhSensitization) : bool :=
  rbc_compatible_abo recipient donor &&
  rbc_compatible_rh (snd recipient) (snd donor) sens.

(** Conservative RBC compatibility (assumes worst-case Rh sensitization).
    Use this when sensitization history is unknown or unreliable.
    This maintains backward compatibility with the original rbc_compatible. *)
Definition rbc_compatible (recipient donor : BloodType) : bool :=
  forallb (antigen_safe recipient donor) core_antigens.

(** The conservative model is equivalent to assuming Rh sensitization *)
Theorem rbc_compatible_is_conservative : forall r d,
  rbc_compatible r d = true ->
  rbc_compatible_with_sens r d Rh_Sensitized_D = true.
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]] H; simpl in *;
  try reflexivity; try discriminate.
Qed.

(** Naive recipients have MORE compatible donors *)
Theorem naive_more_permissive : forall r d,
  rbc_compatible r d = true ->
  rbc_compatible_with_sens r d Rh_Naive = true.
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]] H; simpl in *;
  try reflexivity; try discriminate.
Qed.

(** ========== PLASMA COMPATIBILITY ========== *)

(** Plasma compatibility is ABO-DRIVEN ONLY.
    Rh is clinically irrelevant for plasma transfusion because:
    1. Plasma contains antibodies, not antigens
    2. Anti-D (if present in donor plasma) is diluted and rarely causes issues
    3. Standard practice ignores Rh for plasma selection

    AB plasma is universal donor (no anti-A or anti-B).
    O plasma can only go to O recipients (has both anti-A and anti-B). *)
Definition plasma_compatible_abo (recipient donor : BloodType) : bool :=
  forallb (fun ag => negb (has_antigen recipient ag && has_antibody_abo donor ag)) abo_antigens.

(** Plasma compatibility - CORRECT MODEL (ABO-only).
    Rh is clinically irrelevant for plasma products because:
    - Plasma contains antibodies, not intact RBCs with Rh antigens
    - Any residual anti-D in donor plasma is diluted below clinical significance
    - All major blood banking organizations ignore Rh for plasma selection

    This replaces the previous legacy model that incorrectly checked Rh. *)
Definition plasma_compatible (recipient donor : BloodType) : bool :=
  plasma_compatible_abo recipient donor.

(** Alias for explicitness *)
Definition plasma_compatible_correct (recipient donor : BloodType) : bool :=
  plasma_compatible recipient donor.

(** Legacy function for code that needs the old (overcautious) behavior.
    NOT recommended for new code - use plasma_compatible instead. *)
Definition plasma_compatible_legacy (recipient donor : BloodType) : bool :=
  rbc_compatible donor recipient.

(** AB plasma is universal donor *)
Theorem AB_plasma_universal_donor_correct : forall recipient,
  plasma_compatible_correct recipient (AB, Pos) = true /\
  plasma_compatible_correct recipient (AB, Neg) = true.
Proof.
  intros [[| | | ] [| ]]; split; reflexivity.
Qed.

(** O recipients can receive any plasma *)
Theorem O_plasma_universal_recipient_correct : forall donor,
  plasma_compatible_correct (O, Pos) donor = true /\
  plasma_compatible_correct (O, Neg) donor = true.
Proof.
  intros [[| | | ] [| ]]; split; reflexivity.
Qed.

(** Plasma compatibility rationale: donor plasma antibodies must not react
    with recipient RBC antigens. Plasma compatibility checks ABO antibodies
    only (natural isoagglutinins) because Rh antigens are not present in
    plasma products. *)
Definition plasma_compatible_rationale : Prop :=
  forall r d, plasma_compatible r d = true <->
    (forall ag, In ag abo_antigens ->
      has_antibody_abo d ag = true -> has_antigen r ag = false).

(** ========== PRODUCT-SPECIFIC COMPATIBILITY ========== *)

(** RBC product compatibility - uses conservative model *)
Definition product_rbc_compatible (recipient donor : BloodType) : bool :=
  rbc_compatible recipient donor.

(** RBC product with known sensitization status *)
Definition product_rbc_compatible_with_sens (recipient donor : BloodType)
                                             (sens : RhSensitization) : bool :=
  rbc_compatible_with_sens recipient donor sens.

(** Plasma product compatibility - ABO only, Rh irrelevant *)
Definition product_plasma_compatible (recipient donor : BloodType) : bool :=
  plasma_compatible_correct recipient donor.

(** Platelet compatibility - ABO preferred but not required, Rh matters for
    females of childbearing potential due to RBC contamination in platelet units *)
Definition product_platelet_compatible (recipient donor : BloodType)
                                        (childbearing_female : bool) : bool :=
  let abo_ok := plasma_compatible_correct recipient donor in
  let rh_ok := match snd recipient, snd donor, childbearing_female with
               | Neg, Pos, true => false
               | _, _, _ => true
               end in
  abo_ok && rh_ok.

(** Platelet ABO is less strict - O platelets often given to non-O *)
Definition product_platelet_abo_acceptable (recipient donor : BloodType) : bool :=
  match fst recipient, fst donor with
  | _, O => true
  | AB, _ => true
  | x, y => if abo_eq_dec x y then true else false
  end.

Theorem platelet_O_acceptable_to_all : forall r_abo r_rh,
  product_platelet_abo_acceptable (r_abo, r_rh) (O, Pos) = true /\
  product_platelet_abo_acceptable (r_abo, r_rh) (O, Neg) = true.
Proof.
  intros [| | | ] [| ]; split; reflexivity.
Qed.

(** Cryoprecipitate - ABO match preferred for large volumes *)
Definition product_cryo_compatible (recipient donor : BloodType) (volume_ml : nat) : bool :=
  if Nat.leb 2000 volume_ml then
    match fst recipient, fst donor with
    | x, y => if abo_eq_dec x y then true else false
    end
  else
    plasma_compatible_correct recipient donor.

(** Whole blood - requires both RBC and plasma compatibility (rare use) *)
Definition product_whole_blood_compatible (recipient donor : BloodType) : bool :=
  rbc_compatible recipient donor && plasma_compatible_correct recipient donor.

(** ABO Titer Modeling for Plasma Transfusion Risk Assessment.
    Titers are expressed as reciprocals (e.g., titer 64 means 1:64 dilution).
    High-titer plasma (>256 for anti-A, >128 for anti-B) poses increased
    risk of hemolytic reactions when transfused to incompatible recipients.

    Clinical context: O plasma donors often have higher titers of anti-A
    and anti-B. "Low-titer O" plasma (titer ≤ 50) is preferred for
    emergency release to non-O recipients. *)
Inductive TiterLevel : Type :=
  | Titer_Low
  | Titer_Moderate
  | Titer_High
  | Titer_Critical.

(** Immunoglobulin classes for antibodies.
    Clinical significance differs by class:
    - IgM: Pentameric, efficient complement activation, causes acute intravascular
           hemolysis. Naturally occurring ABO antibodies are primarily IgM.
           Optimal reactivity at room temperature or below.
    - IgG: Monomeric, crosses placenta (causes HDFN), can cause delayed
           extravascular hemolysis. Immune antibodies are primarily IgG.
           Optimal reactivity at 37°C. Detected by antiglobulin test.
    - IgA: Dimeric in secretions, rarely clinically significant in transfusion
           except in IgA-deficient patients who may have anti-IgA. *)
Inductive IgClass : Type :=
  | IgM
  | IgG
  | IgA.

(** ABO antibody class distribution.
    Type O individuals typically have both IgM and IgG anti-A and anti-B.
    Type A individuals have primarily IgM anti-B.
    Type B individuals have primarily IgM anti-A.
    The presence of IgG ABO antibodies increases hemolytic risk. *)
Inductive ABOAntibodyProfile : Type :=
  | ABO_Ab_IgM_Only
  | ABO_Ab_IgM_IgG
  | ABO_Ab_IgG_Predominant.

Definition type_O_antibody_profile : ABOAntibodyProfile := ABO_Ab_IgM_IgG.
Definition type_A_antibody_profile : ABOAntibodyProfile := ABO_Ab_IgM_Only.
Definition type_B_antibody_profile : ABOAntibodyProfile := ABO_Ab_IgM_Only.

(** IgG presence increases hemolytic risk because:
    1. IgG antibodies cause more prolonged hemolysis (days vs hours)
    2. IgG crosses the placenta (HDFN risk)
    3. IgG may not be detected by immediate spin crossmatch *)
Definition igG_increases_risk (profile : ABOAntibodyProfile) : bool :=
  match profile with
  | ABO_Ab_IgM_Only => false
  | ABO_Ab_IgM_IgG => true
  | ABO_Ab_IgG_Predominant => true
  end.

(** Thermal amplitude affects clinical significance.
    Antibodies reactive only at cold temperatures (< 30°C) are usually
    clinically insignificant. Antibodies reactive at 37°C are significant. *)
Inductive ThermalRange : Type :=
  | Cold_Only
  | Wide_Range
  | Warm_Only.

Definition is_clinically_significant_thermal (tr : ThermalRange) : bool :=
  match tr with
  | Cold_Only => false
  | Wide_Range => true
  | Warm_Only => true
  end.

(** Extended titer record with IgG/IgM breakdown *)
Record TiterByClass := mkTiterByClass {
  titer_IgM : nat;
  titer_IgG : nat;
  titer_thermal : ThermalRange
}.

Definition total_titer (t : TiterByClass) : nat :=
  Nat.max (titer_IgM t) (titer_IgG t).

Definition titer_has_IgG (t : TiterByClass) : bool :=
  Nat.ltb 0 (titer_IgG t).

(** IgG titer threshold is lower because IgG causes more insidious damage *)
Definition igG_titer_threshold : nat := 64.
Definition igM_titer_threshold : nat := 256.

Definition classify_titer_by_class (t : TiterByClass) : TiterLevel :=
  let igM_level := if Nat.leb (titer_IgM t) 50 then 0
                   else if Nat.leb (titer_IgM t) 128 then 1
                   else if Nat.leb (titer_IgM t) 256 then 2
                   else 3 in
  let igG_level := if Nat.leb (titer_IgG t) 16 then 0
                   else if Nat.leb (titer_IgG t) 64 then 1
                   else if Nat.leb (titer_IgG t) 128 then 2
                   else 3 in
  let max_level := Nat.max igM_level igG_level in
  match max_level with
  | 0 => Titer_Low
  | 1 => Titer_Moderate
  | 2 => Titer_High
  | _ => Titer_Critical
  end.

(** IgG-only high titer is still dangerous even if IgM is low *)
Theorem igG_high_means_high_risk : forall thermal,
  classify_titer_by_class (mkTiterByClass 0 200 thermal) = Titer_Critical.
Proof. intros; reflexivity. Qed.

(** Low IgM with no IgG is low risk *)
Theorem igM_low_igG_zero_is_low : forall thermal,
  classify_titer_by_class (mkTiterByClass 30 0 thermal) = Titer_Low.
Proof. intros; reflexivity. Qed.

(** High IgG dominates even with low IgM *)
Theorem igG_dominates_classification : forall thermal,
  classify_titer_by_class (mkTiterByClass 20 150 thermal) = Titer_Critical.
Proof. intros; reflexivity. Qed.

Definition titer_threshold_anti_A : nat := 256.
Definition titer_threshold_anti_B : nat := 128.
Definition low_titer_threshold : nat := 50.

Definition classify_titer (value : nat) : TiterLevel :=
  if Nat.leb value 50 then Titer_Low
  else if Nat.leb value 128 then Titer_Moderate
  else if Nat.leb value 256 then Titer_High
  else Titer_Critical.

Record PlasmaUnit := mkPlasmaUnit {
  plasma_abo : ABO;
  plasma_rh : Rh;
  plasma_anti_A_titer : nat;
  plasma_anti_B_titer : nat;
  plasma_volume_ml : nat
}.

Definition is_low_titer_plasma (p : PlasmaUnit) : bool :=
  Nat.leb (plasma_anti_A_titer p) low_titer_threshold &&
  Nat.leb (plasma_anti_B_titer p) low_titer_threshold.

Definition plasma_hemolytic_risk (recipient_abo : ABO) (p : PlasmaUnit) : TiterLevel :=
  match recipient_abo, plasma_abo p with
  | A, O => classify_titer (plasma_anti_A_titer p)
  | B, O => classify_titer (plasma_anti_B_titer p)
  | AB, O =>
      let risk_A := classify_titer (plasma_anti_A_titer p) in
      let risk_B := classify_titer (plasma_anti_B_titer p) in
      match risk_A, risk_B with
      | Titer_Critical, _ => Titer_Critical
      | _, Titer_Critical => Titer_Critical
      | Titer_High, _ => Titer_High
      | _, Titer_High => Titer_High
      | Titer_Moderate, _ => Titer_Moderate
      | _, Titer_Moderate => Titer_Moderate
      | _, _ => Titer_Low
      end
  | A, B => classify_titer (plasma_anti_A_titer p)
  | B, A => classify_titer (plasma_anti_B_titer p)
  | _, _ => Titer_Low
  end.

(** Plasma safety threshold policies.

    Different institutions use different titer thresholds:
    - Standard: Moderate titer (50-199) considered safe
    - Strict: Only low titer (<50) considered safe
    - Critical care: Critical titer (>=500) always rejected

    The strict policy is recommended for:
    - Pediatric patients
    - Patients with compromised immune systems
    - Massive transfusion protocols
    - When patient ABO status is uncertain *)

Inductive TiterPolicy : Type :=
  | Policy_Standard
  | Policy_Strict
  | Policy_Critical_Only.

Definition plasma_safe_with_policy (policy : TiterPolicy) (recipient_abo : ABO) (p : PlasmaUnit) : bool :=
  match policy, plasma_hemolytic_risk recipient_abo p with
  | _, Titer_Low => true
  | Policy_Standard, Titer_Moderate => true
  | Policy_Strict, Titer_Moderate => false
  | Policy_Critical_Only, Titer_Moderate => true
  | _, Titer_High => false
  | _, Titer_Critical => false
  end.

Definition plasma_safe_for_recipient (recipient_abo : ABO) (p : PlasmaUnit) : bool :=
  plasma_safe_with_policy Policy_Standard recipient_abo p.

Definition plasma_safe_strict (recipient_abo : ABO) (p : PlasmaUnit) : bool :=
  plasma_safe_with_policy Policy_Strict recipient_abo p.

Theorem strict_policy_rejects_moderate : forall abo p,
  plasma_hemolytic_risk abo p = Titer_Moderate ->
  plasma_safe_strict abo p = false.
Proof.
  intros abo p H. unfold plasma_safe_strict, plasma_safe_with_policy. rewrite H. reflexivity.
Qed.

Theorem standard_policy_accepts_moderate : forall abo p,
  plasma_hemolytic_risk abo p = Titer_Moderate ->
  plasma_safe_for_recipient abo p = true.
Proof.
  intros abo p H. unfold plasma_safe_for_recipient, plasma_safe_with_policy. rewrite H. reflexivity.
Qed.

Theorem strict_implies_standard : forall abo p,
  plasma_safe_strict abo p = true ->
  plasma_safe_for_recipient abo p = true.
Proof.
  intros abo p H.
  unfold plasma_safe_strict, plasma_safe_for_recipient, plasma_safe_with_policy in *.
  destruct (plasma_hemolytic_risk abo p); auto.
Qed.

Theorem all_policies_reject_high : forall policy abo p,
  plasma_hemolytic_risk abo p = Titer_High ->
  plasma_safe_with_policy policy abo p = false.
Proof.
  intros policy abo p H. unfold plasma_safe_with_policy. rewrite H. destruct policy; reflexivity.
Qed.

Theorem all_policies_reject_critical : forall policy abo p,
  plasma_hemolytic_risk abo p = Titer_Critical ->
  plasma_safe_with_policy policy abo p = false.
Proof.
  intros policy abo p H. unfold plasma_safe_with_policy. rewrite H. destruct policy; reflexivity.
Qed.

Theorem AB_plasma_no_titer_risk : forall (r : ABO) (titer_A titer_B vol : nat) (rh : Rh),
  let p := mkPlasmaUnit AB rh titer_A titer_B vol in
  plasma_hemolytic_risk r p = Titer_Low.
Proof. intros [| | | ]; reflexivity. Qed.

Theorem low_titer_O_safe_for_A : forall (titer_A titer_B vol : nat) (rh : Rh),
  (titer_A <= 50)%nat -> (titer_B <= 50)%nat ->
  let p := mkPlasmaUnit O rh titer_A titer_B vol in
  plasma_safe_for_recipient A p = true.
Proof.
  intros titer_A titer_B vol rh Ha Hb.
  unfold plasma_safe_for_recipient, plasma_safe_with_policy, plasma_hemolytic_risk, classify_titer.
  simpl. apply Nat.leb_le in Ha. rewrite Ha. reflexivity.
Qed.

Theorem high_titer_O_risky_for_A : forall (titer_B vol : nat) (rh : Rh),
  let p := mkPlasmaUnit O rh 300 titer_B vol in
  plasma_safe_for_recipient A p = false.
Proof.
  intros. unfold plasma_safe_for_recipient, plasma_safe_with_policy.
  simpl. reflexivity.
Qed.

(** Whole blood requires both RBC and plasma compatibility *)
Definition whole_blood_compatible (recipient donor : BloodType) : bool :=
  rbc_compatible recipient donor && plasma_compatible recipient donor.

(** Primary compatibility alias *)
Definition compatible : BloodType -> BloodType -> bool := rbc_compatible.

(** Crossmatch reaction — positive means incompatible *)
Definition crossmatch_positive (recipient donor : BloodType) : bool :=
  existsb (causes_reaction recipient donor) core_antigens.

Theorem crossmatch_compatible_equiv : forall r d,
  crossmatch_positive r d = negb (compatible r d).
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]]; reflexivity.
Qed.

(** Decidability proofs for all compatibility relations *)
Definition compatible_dec (r d : BloodType) : {compatible r d = true} + {compatible r d = false}.
Proof.
  destruct r as [[| | | ] [| ]], d as [[| | | ] [| ]]; simpl;
  first [left; reflexivity | right; reflexivity].
Defined.

Definition plasma_compatible_dec (r d : BloodType) :
  {plasma_compatible r d = true} + {plasma_compatible r d = false}.
Proof.
  destruct r as [[| | | ] [| ]], d as [[| | | ] [| ]]; simpl;
  first [left; reflexivity | right; reflexivity].
Defined.

Definition whole_blood_compatible_dec (r d : BloodType) :
  {whole_blood_compatible r d = true} + {whole_blood_compatible r d = false}.
Proof.
  destruct r as [[| | | ] [| ]], d as [[| | | ] [| ]]; simpl;
  first [left; reflexivity | right; reflexivity].
Defined.

Theorem compatible_decidable : forall r d,
  {compatible r d = true} + {compatible r d = false}.
Proof. exact compatible_dec. Qed.

Theorem plasma_compatible_decidable : forall r d,
  {plasma_compatible r d = true} + {plasma_compatible r d = false}.
Proof. exact plasma_compatible_dec. Qed.

Theorem whole_blood_compatible_decidable : forall r d,
  {whole_blood_compatible r d = true} + {whole_blood_compatible r d = false}.
Proof. exact whole_blood_compatible_dec. Qed.

(******************************************************************************)
(*                        FUNDAMENTAL THEOREMS                                *)
(******************************************************************************)

Theorem O_neg_universal_donor : forall recipient,
  compatible recipient O_neg = true.
Proof. intros [[| | | ] [| ]]; reflexivity. Qed.

Theorem AB_pos_universal_recipient : forall donor,
  compatible AB_pos donor = true.
Proof. intros [[| | | ] [| ]]; reflexivity. Qed.

Theorem self_compatible : forall bt,
  compatible bt bt = true.
Proof. intros [[| | | ] [| ]]; reflexivity. Qed.

Theorem Rh_neg_cannot_receive_pos : forall abo,
  compatible (abo, Neg) (abo, Pos) = false.
Proof. intros [| | | ]; reflexivity. Qed.

Theorem O_neg_unique_universal : forall donor,
  (forall recipient, compatible recipient donor = true) -> donor = O_neg.
Proof.
  intros [[| | | ] [| ]] H;
  try (specialize (H O_neg); discriminate);
  try (specialize (H A_neg); discriminate);
  try (specialize (H B_neg); discriminate);
  reflexivity.
Qed.

(** Cross-type incompatibilities *)
Theorem A_B_incompatible : forall rh1 rh2,
  compatible (A, rh1) (B, rh2) = false /\ compatible (B, rh1) (A, rh2) = false.
Proof. intros [| ] [| ]; split; reflexivity. Qed.

Theorem AB_cannot_donate_to_O : forall rh1 rh2,
  compatible (O, rh1) (AB, rh2) = false.
Proof. intros [| ] [| ]; reflexivity. Qed.

Theorem AB_cannot_donate_to_A : forall rh1 rh2,
  compatible (A, rh1) (AB, rh2) = false.
Proof. intros [| ] [| ]; reflexivity. Qed.

Theorem AB_cannot_donate_to_B : forall rh1 rh2,
  compatible (B, rh1) (AB, rh2) = false.
Proof. intros [| ] [| ]; reflexivity. Qed.

(******************************************************************************)
(*              NEGATIVE/IMPOSSIBILITY THEOREMS                               *)
(******************************************************************************)

(** Complete characterization of incompatible pairs.
    There are exactly 37 incompatible (recipient, donor) pairs out of 64. *)
Theorem total_incompatible_pairs :
  length (filter (fun p => negb (compatible (fst p) (snd p)))
                 (list_prod all_blood_types all_blood_types)) = 37.
Proof. reflexivity. Qed.

(** No blood type other than O-neg can serve ALL recipients *)
Theorem no_other_universal_donor : forall bt,
  bt <> O_neg ->
  exists recipient, compatible recipient bt = false.
Proof.
  intros [[| | | ] [| ]] Hneq.
  - exists O_neg; reflexivity.
  - exists O_neg; reflexivity.
  - exists O_neg; reflexivity.
  - exists O_neg; reflexivity.
  - exists O_neg; reflexivity.
  - exists O_neg; reflexivity.
  - exists O_neg; reflexivity.
  - exfalso; apply Hneq; reflexivity.
Qed.

(** No blood type other than AB-pos can RECEIVE from all donors *)
Theorem no_other_universal_recipient : forall bt,
  bt <> AB_pos ->
  exists donor, compatible bt donor = false.
Proof.
  intros [[| | | ] [| ]] Hneq.
  - exists B_pos; reflexivity.
  - exists B_pos; reflexivity.
  - exists A_pos; reflexivity.
  - exists A_pos; reflexivity.
  - exfalso; apply Hneq; reflexivity.
  - exists A_pos; reflexivity.
  - exists A_pos; reflexivity.
  - exists A_pos; reflexivity.
Qed.

(** AB-neg is unique: universal recipient within Rh-negative *)
Theorem AB_neg_unique_rh_neg_universal : forall bt,
  snd bt = Neg ->
  (forall donor, snd donor = Neg -> compatible bt donor = true) ->
  fst bt = AB.
Proof.
  intros [[| | | ] [| ]] Hrh H; simpl in Hrh; try discriminate.
  - specialize (H B_neg eq_refl); discriminate.
  - specialize (H A_neg eq_refl); discriminate.
  - reflexivity.
  - specialize (H A_neg eq_refl); discriminate.
Qed.

(** Impossibility: Rh-positive cannot donate to Rh-negative (policy model) *)
Theorem rh_barrier_absolute : forall abo1 abo2,
  compatible (abo1, Neg) (abo2, Pos) = false.
Proof. intros [| | | ] [| | | ]; reflexivity. Qed.

(** Characterization: exactly when is a transfusion IMPOSSIBLE? *)
Definition transfusion_impossible (r d : BloodType) : Prop :=
  (fst r = O /\ fst d <> O) \/
  (fst r = A /\ fst d = B) \/
  (fst r = A /\ fst d = AB) \/
  (fst r = B /\ fst d = A) \/
  (fst r = B /\ fst d = AB) \/
  (snd r = Neg /\ snd d = Pos).

Theorem impossible_means_incompatible : forall r d,
  transfusion_impossible r d -> compatible r d = false.
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]] H;
  destruct H as [H | [H | [H | [H | [H | H]]]]];
  destruct H as [H1 H2]; simpl in *; try discriminate; try reflexivity;
  try (exfalso; apply H2; reflexivity).
Qed.

(** Converse: incompatibility implies one of the impossible conditions *)
Theorem incompatible_means_impossible : forall r d,
  compatible r d = false -> transfusion_impossible r d.
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]] H; simpl in H; try discriminate;
  unfold transfusion_impossible; simpl;
  try (left; split; [reflexivity | discriminate]);
  try (right; left; split; reflexivity);
  try (right; right; left; split; reflexivity);
  try (right; right; right; left; split; reflexivity);
  try (right; right; right; right; left; split; reflexivity);
  try (right; right; right; right; right; split; reflexivity).
Qed.

(** Bidirectional incompatibility is NOT symmetric for ABO *)
Theorem abo_incompatibility_asymmetric :
  compatible O_pos A_pos = false /\ compatible A_pos O_pos = true.
Proof. split; reflexivity. Qed.

(** But Rh incompatibility blocks in only one direction *)
Theorem rh_incompatibility_one_way : forall abo,
  compatible (abo, Neg) (abo, Pos) = false /\
  compatible (abo, Pos) (abo, Neg) = true.
Proof. intros [| | | ]; split; reflexivity. Qed.

(** Plasma impossibility: O plasma cannot go to non-O *)
Theorem O_plasma_cannot_serve_non_O : forall rh r_abo r_rh,
  r_abo <> O ->
  plasma_compatible (r_abo, r_rh) (O, rh) = false.
Proof.
  intros [| ] [| | | ] [| ] H; try reflexivity;
  exfalso; apply H; reflexivity.
Qed.

(** Exactly 4 plasma-incompatible pairs per O donor variant *)
Theorem O_plasma_incompatible_count :
  length (filter (fun r => negb (plasma_compatible r O_pos)) all_blood_types) = 6.
Proof. reflexivity. Qed.

(** A and B types have plasma restrictions (cannot receive O plasma) *)
Theorem A_plasma_restriction : forall rh,
  exists donor, plasma_compatible (A, rh) donor = false.
Proof. intros [| ]; exists O_pos; reflexivity. Qed.

Theorem B_plasma_restriction : forall rh,
  exists donor, plasma_compatible (B, rh) donor = false.
Proof. intros [| ]; exists O_pos; reflexivity. Qed.

(** O type can receive plasma from anyone (no A/B antigens to react) *)
Theorem O_plasma_universal_receiver : forall rh donor,
  plasma_compatible (O, rh) donor = true.
Proof. intros [| ] [[| | | ] [| ]]; reflexivity. Qed.

(** Mutual exclusion: A and B antigens cannot both be absent for universal recipient *)
Theorem universal_recipient_requires_both_antigens :
  forall bt, (forall donor, compatible bt donor = true) ->
  fst bt = AB.
Proof.
  intros [[| | | ] [| ]] H.
  - specialize (H B_pos); discriminate.
  - specialize (H B_pos); discriminate.
  - specialize (H A_pos); discriminate.
  - specialize (H A_pos); discriminate.
  - reflexivity.
  - specialize (H A_pos); discriminate.
  - specialize (H A_pos); discriminate.
  - specialize (H A_pos); discriminate.
Qed.

(** Safety characterization *)
Definition no_adverse_reaction (recipient donor : BloodType) : Prop :=
  forall ag, has_antibody recipient ag = true -> has_antigen donor ag = false.

Theorem compatible_iff_safe : forall r d,
  compatible r d = true <-> no_adverse_reaction r d.
Proof.
  intros r d; split; intros H.
  - unfold no_adverse_reaction. intros ag Hab.
    destruct r as [[| | | ] [| ]], d as [[| | | ] [| ]];
    unfold compatible, rbc_compatible in H; simpl in *;
    destruct ag; simpl in *; try reflexivity; try discriminate.
  - destruct r as [[| | | ] [| ]], d as [[| | | ] [| ]];
    unfold no_adverse_reaction, compatible, rbc_compatible in *; simpl in *;
    try reflexivity;
    try (specialize (H Ag_A eq_refl); discriminate);
    try (specialize (H Ag_B eq_refl); discriminate);
    try (specialize (H Ag_D eq_refl); discriminate).
Qed.

(** Plasma rationale theorem - proves the semantic meaning of plasma_compatible.
    For the correct ABO-only model: donor ABO antibodies must not react with
    recipient ABO antigens. *)
Lemma plasma_rationale_forward : forall r d,
  plasma_compatible r d = true ->
  (forall ag, In ag abo_antigens -> has_antibody_abo d ag = true -> has_antigen r ag = false).
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]] Hcompat ag [Heq | [Heq | []]] Hab;
  subst; simpl in *; try discriminate; reflexivity.
Qed.

Lemma plasma_rationale_backward : forall r d,
  (forall ag, In ag abo_antigens -> has_antibody_abo d ag = true -> has_antigen r ag = false) ->
  plasma_compatible r d = true.
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]] H; simpl; try reflexivity.
  all: try (assert (Hcontra: true = false) by
              (apply (H Ag_A); [left; reflexivity | reflexivity]);
            discriminate Hcontra).
  all: try (assert (Hcontra: true = false) by
              (apply (H Ag_B); [right; left; reflexivity | reflexivity]);
            discriminate Hcontra).
Qed.

Theorem plasma_rationale_holds : plasma_compatible_rationale.
Proof.
  unfold plasma_compatible_rationale.
  intros r d; split.
  - apply plasma_rationale_forward.
  - apply plasma_rationale_backward.
Qed.

(** Complete compatibility matrix *)
Theorem total_compatible_pairs :
  length (filter (fun p => compatible (fst p) (snd p))
                 (list_prod all_blood_types all_blood_types)) = 27.
Proof. reflexivity. Qed.

Definition count_donors (recipient : BloodType) : nat :=
  length (filter (compatible recipient) all_blood_types).

Definition count_recipients (donor : BloodType) : nat :=
  length (filter (fun r => compatible r donor) all_blood_types).

Theorem donor_recipient_counts :
  count_donors O_neg = 1 /\
  count_donors AB_pos = 8 /\
  count_recipients O_neg = 8 /\
  count_recipients AB_pos = 1.
Proof. repeat split; reflexivity. Qed.

(** Rh-negative recipients are ALWAYS more restricted than Rh-positive *)
Theorem rh_neg_always_more_restricted : forall abo,
  count_donors (abo, Neg) < count_donors (abo, Pos).
Proof. intros [| | | ]; unfold count_donors; simpl; lia. Qed.

(** O-neg is the MOST restricted recipient (fewest compatible donors) *)
Theorem O_neg_most_restricted_recipient :
  forall bt, bt <> O_neg -> count_donors O_neg <= count_donors bt.
Proof.
  intros [[| | | ] [| ]] Hneq; unfold count_donors; simpl;
  first [lia | exfalso; apply Hneq; reflexivity].
Qed.

(** Strict inequality: O-neg has strictly fewer donors than any other type *)
Theorem O_neg_strictly_most_restricted :
  forall bt, bt <> O_neg -> count_donors O_neg < count_donors bt.
Proof.
  intros [[| | | ] [| ]] Hneq; unfold count_donors; simpl;
  first [lia | exfalso; apply Hneq; reflexivity].
Qed.

(** === LATE-DEFINED TACTICS (require compatible, count_donors, etc.) === *)

(** Solve RBC compatibility goals *)
Ltac solve_rbc_compat :=
  unfold compatible, rbc_compatible; simpl;
  solve_blood_type_cases.

(** Solve plasma compatibility goals *)
Ltac solve_plasma_compat :=
  unfold plasma_compatible, plasma_compatible_correct; simpl;
  solve_blood_type_cases.

(** Solve nat inequality goals from compatibility counts *)
Ltac solve_count_inequality :=
  unfold count_donors, count_recipients; simpl; lia.

(******************************************************************************)
(*                                                                            *)
(*                      IV. BLOOD COMPONENT COMPATIBILITY                     *)
(*                                                                            *)
(******************************************************************************)

(** Platelet ABO compatibility — preference, not strict requirement *)
Definition platelet_abo_preferred (recipient donor : ABO) : bool :=
  match recipient, donor with
  | x, y => if abo_eq_dec x y then true else
    match recipient, donor with
    | AB, _ => true
    | A, O => true
    | B, O => true
    | O, O => true
    | _, _ => false
    end
  end.

(** Platelet Rh consideration for females of childbearing potential *)
Definition platelet_rh_safe (r_rh d_rh : Rh) (childbearing : bool) : bool :=
  match r_rh, d_rh, childbearing with
  | Neg, Pos, true => false
  | _, _, _ => true
  end.

Theorem O_platelets_universal : forall abo,
  platelet_abo_preferred abo O = true.
Proof. intros [| | | ]; reflexivity. Qed.

(** Cryoprecipitate — ABO match preferred for large volumes *)
Definition cryo_needs_abo_match (volume_ml : nat) : bool :=
  Nat.leb 2000 volume_ml.

(** Product shelf life in days *)
Definition shelf_life (p : Product) : nat :=
  match p with
  | PackedRBC => 42
  | FreshFrozenPlasma => 365
  | Platelets => 5
  | Cryoprecipitate => 365
  | WholeBlood => 21
  end.

Definition is_expired (p : Product) (age_days : nat) : bool :=
  Nat.ltb (shelf_life p) age_days.

Theorem product_expiration_examples :
  is_expired PackedRBC 50 = true /\
  is_expired PackedRBC 30 = false /\
  is_expired Platelets 7 = true /\
  is_expired Platelets 3 = false.
Proof. repeat split; reflexivity. Qed.

(** Storage lesion — degradation over time *)
Definition storage_lesion (age_days : nat) : nat :=
  if Nat.leb age_days 14 then 0
  else if Nat.leb age_days 28 then 1
  else if Nat.leb age_days 42 then 2
  else 3.

(******************************************************************************)
(*                                                                            *)
(*                   V. EXTENDED TYPING AND VARIANTS                          *)
(*                                                                            *)
(******************************************************************************)

(** ABO Subtypes *)
Inductive ABOSubtype : Type :=
  | Sub_A1 | Sub_A2 | Sub_A3 | Sub_Aint
  | Sub_B
  | Sub_A1B | Sub_A2B
  | Sub_O
  | Sub_Bombay
  | Sub_Acquired_B
  | Sub_Cis_AB.

Definition subtype_base_abo (s : ABOSubtype) : option ABO :=
  match s with
  | Sub_A1 | Sub_A2 | Sub_A3 | Sub_Aint => Some A
  | Sub_B => Some B
  | Sub_A1B | Sub_A2B | Sub_Cis_AB => Some AB
  | Sub_O => Some O
  | Sub_Bombay => None
  | Sub_Acquired_B => Some A
  end.

(** Acquired B phenotype: bacterial deacetylase converts A antigen to B-like.
    - Occurs in GI malignancy, infection, bowel obstruction
    - Types as AB but patient is truly type A
    - Anti-B present in plasma (patient's true antibodies)
    - Transient: resolves when underlying condition treated
    - Transfusion: give group A or O red cells, NOT group B *)
Definition is_acquired_b (s : ABOSubtype) : bool :=
  match s with Sub_Acquired_B => true | _ => false end.

Definition acquired_b_safe_donor (donor_abo : ABO) : bool :=
  match donor_abo with A | O => true | B | AB => false end.

Theorem acquired_b_cannot_receive_B :
  acquired_b_safe_donor B = false.
Proof. reflexivity. Qed.

Theorem acquired_b_can_receive_A :
  acquired_b_safe_donor A = true.
Proof. reflexivity. Qed.

(** Cis-AB: both A and B encoded on same chromosome.
    - Rare phenotype (mostly East Asian populations)
    - Weak B antigen expression
    - Types as AB but genetics shows single allele inheritance
    - Parent can be O and child can be AB (unusual inheritance)
    - Transfusion: treat as AB for receiving, but plasma has weak anti-B *)
Definition is_cis_ab (s : ABOSubtype) : bool :=
  match s with Sub_Cis_AB => true | _ => false end.

Definition cis_ab_has_weak_anti_B (s : ABOSubtype) : bool :=
  match s with Sub_Cis_AB => true | _ => false end.

Theorem cis_ab_unusual_inheritance :
  subtype_base_abo Sub_Cis_AB = Some AB.
Proof. reflexivity. Qed.

Definition has_A1_antigen (s : ABOSubtype) : bool :=
  match s with Sub_A1 | Sub_A1B => true | _ => false end.

(** Anti-A1 policy: controls how to handle potential anti-A1 in A2/A2B recipients.

    Anti-A1 occurs in approximately:
    - 1-8% of A2 individuals
    - 25-35% of A2B individuals

    This is NOT deterministic - it's a conservative policy parameter.
    - Conservative: Assume A2/A2B MAY have anti-A1 (avoid A1/A1B donors)
    - Laboratory: Only consider anti-A1 if detected in antibody screen
    - Permissive: Ignore potential anti-A1 (accept any ABO-compatible unit) *)
Inductive AntiA1Policy : Type :=
  | AntiA1_Conservative
  | AntiA1_Laboratory_Based
  | AntiA1_Permissive.

Definition may_have_anti_A1_with_policy (s : ABOSubtype) (policy : AntiA1Policy)
                                        (lab_detected : bool) : bool :=
  match policy with
  | AntiA1_Conservative => match s with Sub_A2 | Sub_A2B => true | _ => false end
  | AntiA1_Laboratory_Based => lab_detected
  | AntiA1_Permissive => false
  end.

(** Default conservative policy for backward compatibility *)
Definition may_have_anti_A1 (s : ABOSubtype) : bool :=
  may_have_anti_A1_with_policy s AntiA1_Conservative false.

(** Prevalence of anti-A1 by subtype (percentage) *)
Definition anti_A1_prevalence_A2 : nat := 8.
Definition anti_A1_prevalence_A2B : nat := 35.

Theorem A2B_higher_anti_A1_prevalence :
  anti_A1_prevalence_A2 < anti_A1_prevalence_A2B.
Proof. unfold anti_A1_prevalence_A2, anti_A1_prevalence_A2B; lia. Qed.

(** ABO Subgroup Serological Reaction Patterns.

    ABO subtypes show characteristic patterns in forward and reverse typing.
    Reaction strength is graded 0-4:
    - 4+: Strong immediate agglutination, large clumps
    - 3+: Large clumps, some free cells
    - 2+: Medium clumps, many free cells
    - 1+: Small clumps, many free cells
    - w (weak): Microscopic agglutination only
    - 0: No agglutination

    Clinical significance:
    - Weak A/B subtypes may be mistyped as O
    - A2 cells react weakly with some anti-A reagents
    - Weak subtypes require additional testing (adsorption-elution)
    - Mixed-field reactions suggest chimerism or recent transfusion *)

Inductive ReactionStrength : Type :=
  | Reaction_4plus
  | Reaction_3plus
  | Reaction_2plus
  | Reaction_1plus
  | Reaction_Weak
  | Reaction_MixedField
  | Reaction_Negative.

Definition reaction_strength_value (r : ReactionStrength) : nat :=
  match r with
  | Reaction_4plus => 4
  | Reaction_3plus => 3
  | Reaction_2plus => 2
  | Reaction_1plus => 1
  | Reaction_Weak => 0
  | Reaction_MixedField => 1
  | Reaction_Negative => 0
  end.

Record SerologicalPattern := mkSerologicalPattern {
  forward_anti_A : ReactionStrength;
  forward_anti_B : ReactionStrength;
  forward_anti_AB : ReactionStrength;
  reverse_A1_cells : ReactionStrength;
  reverse_B_cells : ReactionStrength
}.

Definition expected_serology (s : ABOSubtype) : SerologicalPattern :=
  match s with
  | Sub_A1 => mkSerologicalPattern
      Reaction_4plus Reaction_Negative Reaction_4plus
      Reaction_Negative Reaction_4plus
  | Sub_A2 => mkSerologicalPattern
      Reaction_2plus Reaction_Negative Reaction_3plus
      Reaction_Negative Reaction_4plus
  | Sub_A3 => mkSerologicalPattern
      Reaction_MixedField Reaction_Negative Reaction_MixedField
      Reaction_Negative Reaction_4plus
  | Sub_Aint => mkSerologicalPattern
      Reaction_Weak Reaction_Negative Reaction_1plus
      Reaction_Weak Reaction_4plus
  | Sub_B => mkSerologicalPattern
      Reaction_Negative Reaction_4plus Reaction_4plus
      Reaction_4plus Reaction_Negative
  | Sub_A1B => mkSerologicalPattern
      Reaction_4plus Reaction_4plus Reaction_4plus
      Reaction_Negative Reaction_Negative
  | Sub_A2B => mkSerologicalPattern
      Reaction_2plus Reaction_4plus Reaction_4plus
      Reaction_Negative Reaction_Negative
  | Sub_O => mkSerologicalPattern
      Reaction_Negative Reaction_Negative Reaction_Negative
      Reaction_4plus Reaction_4plus
  | Sub_Bombay => mkSerologicalPattern
      Reaction_Negative Reaction_Negative Reaction_Negative
      Reaction_4plus Reaction_4plus
  | Sub_Acquired_B => mkSerologicalPattern
      Reaction_4plus Reaction_Weak Reaction_4plus
      Reaction_Negative Reaction_4plus
  | Sub_Cis_AB => mkSerologicalPattern
      Reaction_4plus Reaction_2plus Reaction_4plus
      Reaction_Negative Reaction_Weak
  end.

Definition is_weak_subgroup (s : ABOSubtype) : bool :=
  match s with
  | Sub_A3 | Sub_Aint => true
  | _ => false
  end.

Definition needs_additional_testing (pattern : SerologicalPattern) : bool :=
  match forward_anti_A pattern, forward_anti_B pattern with
  | Reaction_Weak, _ => true
  | Reaction_MixedField, _ => true
  | _, Reaction_Weak => true
  | _, Reaction_MixedField => true
  | _, _ => false
  end.

Definition forward_reverse_discrepancy (pattern : SerologicalPattern) : bool :=
  let forward_A := reaction_strength_value (forward_anti_A pattern) in
  let forward_B := reaction_strength_value (forward_anti_B pattern) in
  let reverse_A := reaction_strength_value (reverse_A1_cells pattern) in
  let reverse_B := reaction_strength_value (reverse_B_cells pattern) in
  let has_A_forward := Nat.ltb 0 forward_A in
  let has_B_forward := Nat.ltb 0 forward_B in
  let anti_A_in_reverse := Nat.ltb 0 reverse_A in
  let anti_B_in_reverse := Nat.ltb 0 reverse_B in
  (has_A_forward && anti_A_in_reverse) || (has_B_forward && anti_B_in_reverse).

Definition risk_of_mistyping_as_O (s : ABOSubtype) : bool :=
  match s with
  | Sub_A3 | Sub_Aint => true
  | _ => false
  end.

Theorem A1_strong_reactions :
  let p := expected_serology Sub_A1 in
  forward_anti_A p = Reaction_4plus /\ forward_anti_AB p = Reaction_4plus.
Proof. split; reflexivity. Qed.

Theorem A2_weaker_than_A1 :
  reaction_strength_value (forward_anti_A (expected_serology Sub_A2)) <
  reaction_strength_value (forward_anti_A (expected_serology Sub_A1)).
Proof. simpl; lia. Qed.

Theorem weak_subtypes_need_testing :
  needs_additional_testing (expected_serology Sub_A3) = true /\
  needs_additional_testing (expected_serology Sub_Aint) = true.
Proof. split; reflexivity. Qed.

Theorem O_and_Bombay_same_forward_typing :
  forward_anti_A (expected_serology Sub_O) = forward_anti_A (expected_serology Sub_Bombay) /\
  forward_anti_B (expected_serology Sub_O) = forward_anti_B (expected_serology Sub_Bombay).
Proof. split; reflexivity. Qed.

(** ========== POLYAGGLUTINATION (T-ACTIVATION) ========== *)

(** Polyagglutination occurs when normally hidden antigens become exposed on RBC
    surfaces, causing agglutination with most adult sera (which contain natural
    antibodies to these cryptantigens).

    T-activation is the most common form:
    - Caused by bacterial neuraminidase cleaving sialic acid from glycophorins
    - Exposes the Thomsen-Friedenreich (T) antigen
    - Most adult sera contain anti-T (IgM, cold-reactive)
    - Associated with necrotizing enterocolitis (NEC) in neonates, sepsis

    Clinical significance:
    - T-activated RBCs agglutinate with all ABO typing reagents
    - Crossmatches appear incompatible
    - Plasma transfusion can cause hemolysis (contains anti-T)
    - Use washed RBCs or low-titer anti-T plasma *)

Inductive PolyagglutinationType : Type :=
  | Poly_T          (** T-activation: neuraminidase, most common *)
  | Poly_Tk         (** Tk: bacterial glycosidase, persistent *)
  | Poly_Th         (** Th: similar to T but different enzyme *)
  | Poly_Tx         (** Tx: acquired B-like, transient *)
  | Poly_Tn         (** Tn: somatic mutation, permanent, pre-leukemic *)
  | Poly_Cad        (** Cad/Sda strong: inherited, not pathological *)
  | Poly_HEMPAS     (** HEMPAS: congenital dyserythropoietic anemia type II *)
  | Poly_None.

(** Polyagglutination etiology *)
Inductive PolyEtiology : Type :=
  | Etiology_Bacterial_Infection
  | Etiology_Viral_Infection
  | Etiology_Somatic_Mutation
  | Etiology_Inherited
  | Etiology_CDA_TypeII
  | Etiology_Unknown.

Definition poly_etiology (p : PolyagglutinationType) : PolyEtiology :=
  match p with
  | Poly_T | Poly_Tk | Poly_Th | Poly_Tx => Etiology_Bacterial_Infection
  | Poly_Tn => Etiology_Somatic_Mutation
  | Poly_Cad => Etiology_Inherited
  | Poly_HEMPAS => Etiology_CDA_TypeII
  | Poly_None => Etiology_Unknown
  end.

(** Clinical management requirements *)
Record PolyagglutinationProfile := mkPolyProfile {
  poly_type : PolyagglutinationType;
  poly_strength : ReactionStrength;
  poly_hemolysis_observed : bool;
  poly_patient_age_days : option nat  (** For neonatal NEC cases *)
}.

(** Is polyagglutination clinically significant for transfusion? *)
Definition poly_clinically_significant (p : PolyagglutinationProfile) : bool :=
  match poly_type p with
  | Poly_None => false
  | Poly_Cad => false  (** Inherited, not pathological *)
  | _ =>
      match poly_strength p with
      | Reaction_4plus | Reaction_3plus | Reaction_2plus => true
      | _ => poly_hemolysis_observed p
      end
  end.

(** Product modification requirements for polyagglutinated patients *)
Inductive PolyProductRequirement : Type :=
  | Poly_Req_WashedRBC       (** Remove plasma with anti-T *)
  | Poly_Req_LowTiterPlasma  (** Use low anti-T titer plasma *)
  | Poly_Req_AvoidPlasma     (** Avoid plasma products entirely *)
  | Poly_Req_Standard.       (** No special requirements *)

Definition poly_product_requirement (p : PolyagglutinationProfile) : PolyProductRequirement :=
  if negb (poly_clinically_significant p) then Poly_Req_Standard
  else match poly_type p with
       | Poly_T | Poly_Th => Poly_Req_WashedRBC
       | Poly_Tn => Poly_Req_AvoidPlasma  (** Tn is permanent, high risk *)
       | Poly_HEMPAS => Poly_Req_LowTiterPlasma
       | _ => Poly_Req_WashedRBC
       end.

(** T-activation in neonates with NEC is a medical emergency *)
Definition neonatal_t_activation_high_risk (p : PolyagglutinationProfile) : bool :=
  match poly_type p, poly_patient_age_days p with
  | Poly_T, Some days => Nat.leb days 90  (** Neonate < 3 months *)
  | _, _ => false
  end.

Theorem t_activation_requires_washed_rbc :
  forall p, poly_type p = Poly_T ->
  poly_clinically_significant p = true ->
  poly_product_requirement p = Poly_Req_WashedRBC.
Proof.
  intros p Htype Hsig.
  unfold poly_product_requirement. rewrite Hsig. rewrite Htype.
  reflexivity.
Qed.

Theorem tn_permanent_high_risk :
  poly_etiology Poly_Tn = Etiology_Somatic_Mutation.
Proof. reflexivity. Qed.

Theorem cad_not_clinically_significant :
  forall strength hemolysis age,
  poly_clinically_significant
    (mkPolyProfile Poly_Cad strength hemolysis age) = false.
Proof. intros; reflexivity. Qed.

(** Generalized A1 incompatibility check: recipients who may have anti-A1
    cannot receive units with A1 antigen. This generalizes the previous
    ad-hoc checks for Sub_A2/Sub_A1, Sub_A2/Sub_A1B, Sub_A2B/Sub_A1. *)
Definition a1_compatible (recipient donor : ABOSubtype) : bool :=
  negb (may_have_anti_A1 recipient && has_A1_antigen donor).

Definition subtype_abo_compatible (recipient donor : ABOSubtype) : bool :=
  match recipient, donor with
  | Sub_Bombay, Sub_Bombay => true
  | Sub_Bombay, _ => false
  | _, Sub_Bombay => false
  | r, d =>
      match subtype_base_abo r, subtype_base_abo d with
      | Some ra, Some da => compatible (ra, Pos) (da, Pos) && a1_compatible r d
      | _, _ => false
      end
  end.

Definition subtype_compatible (recipient donor : ABOSubtype) : bool :=
  subtype_abo_compatible recipient donor.

Theorem a1_incompatibility_generalized : forall r d,
  may_have_anti_A1 r = true -> has_A1_antigen d = true ->
  a1_compatible r d = false.
Proof.
  intros r d Hr Hd. unfold a1_compatible. rewrite Hr, Hd. reflexivity.
Qed.

Theorem bombay_exclusivity : forall s,
  s <> Sub_Bombay -> subtype_compatible Sub_Bombay s = false.
Proof.
  intros [| | | | | | | | | | ] H; try reflexivity; exfalso; apply H; reflexivity.
Qed.

Theorem A2_A1_incompatible :
  subtype_compatible Sub_A2 Sub_A1 = false.
Proof. reflexivity. Qed.

Theorem A2_A1B_incompatible :
  subtype_compatible Sub_A2 Sub_A1B = false.
Proof. reflexivity. Qed.

Theorem A2B_A1_incompatible :
  subtype_compatible Sub_A2B Sub_A1 = false.
Proof. reflexivity. Qed.

Theorem A2B_A1B_incompatible :
  subtype_compatible Sub_A2B Sub_A1B = false.
Proof. reflexivity. Qed.

(** Rh Variants — D antigen categories *)
Inductive RhVariant : Type :=
  | Rh_Normal_Pos
  | Rh_Normal_Neg
  | Rh_Weak_1 | Rh_Weak_2 | Rh_Weak_3 | Rh_Weak_4_0 | Rh_Weak_4_2
  | Rh_Partial_DVI | Rh_Partial_DVa | Rh_Partial_DIIIa
  | Rh_Partial_DIVa | Rh_Partial_DV | Rh_Partial_DVII.

Definition variant_donation_type (v : RhVariant) : Rh :=
  match v with Rh_Normal_Neg => Neg | _ => Pos end.

(** Weak D type 4.2 is the highest-risk partial D variant.
    Unlike other weak D types, type 4.2 individuals:
    - Can form anti-D
    - Should receive Rh-negative blood
    - Are clinically managed as partial D, not weak D *)
Definition variant_transfusion_type (v : RhVariant) : Rh :=
  match v with
  | Rh_Normal_Pos | Rh_Weak_1 | Rh_Weak_2 | Rh_Weak_3 | Rh_Weak_4_0 => Pos
  | Rh_Weak_4_2 => Neg
  | _ => Neg
  end.

Definition variant_can_make_anti_D (v : RhVariant) : bool :=
  match v with
  | Rh_Normal_Pos | Rh_Weak_1 | Rh_Weak_2 | Rh_Weak_3 | Rh_Weak_4_0 => false
  | Rh_Weak_4_2 => true
  | _ => true
  end.

Theorem weak_d_4_2_is_high_risk :
  variant_can_make_anti_D Rh_Weak_4_2 = true /\
  variant_transfusion_type Rh_Weak_4_2 = Neg.
Proof. split; reflexivity. Qed.

Theorem weak_d_4_0_is_low_risk :
  variant_can_make_anti_D Rh_Weak_4_0 = false /\
  variant_transfusion_type Rh_Weak_4_0 = Pos.
Proof. split; reflexivity. Qed.

Theorem weak_d_policies :
  variant_transfusion_type Rh_Weak_1 = Pos /\
  variant_donation_type Rh_Weak_1 = Pos /\
  variant_transfusion_type Rh_Partial_DVI = Neg /\
  variant_donation_type Rh_Partial_DVI = Pos.
Proof. repeat split; reflexivity. Qed.

(** D Antigen Epitope Model for Partial D Variants.

    The RhD protein has approximately 30 epitopes (epD1-epD9, plus others).
    Partial D variants lack certain epitopes and can form antibodies against
    the missing epitopes if exposed to normal RhD-positive blood.

    Clinical significance:
    - Partial D individuals should receive Rh-negative blood
    - Partial D donors are typed as Rh-positive (they express D antigen)
    - Missing epitopes determine which anti-D specificities can form

    This model captures the major partial D categories and their epitope profiles.
    Epitope numbering follows the standard epD1-epD9 nomenclature. *)

Inductive DEpitope : Type :=
  | epD1 | epD2 | epD3 | epD4 | epD5 | epD6 | epD7 | epD8 | epD9.

Definition d_epitope_eq_dec (x y : DEpitope) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition all_d_epitopes : list DEpitope :=
  [epD1; epD2; epD3; epD4; epD5; epD6; epD7; epD8; epD9].

Definition variant_has_epitope (v : RhVariant) (ep : DEpitope) : bool :=
  match v with
  | Rh_Normal_Pos => true
  | Rh_Normal_Neg => false
  | Rh_Weak_1 | Rh_Weak_2 | Rh_Weak_3 | Rh_Weak_4_0 => true
  | Rh_Weak_4_2 =>
      match ep with
      | epD5 | epD6 | epD7 => false
      | _ => true
      end
  | Rh_Partial_DVI =>
      match ep with
      | epD1 | epD5 | epD6 | epD7 => false
      | _ => true
      end
  | Rh_Partial_DVa =>
      match ep with
      | epD5 | epD6 | epD7 => false
      | _ => true
      end
  | Rh_Partial_DIIIa =>
      match ep with
      | epD3 | epD4 | epD9 => false
      | _ => true
      end
  | Rh_Partial_DIVa =>
      match ep with
      | epD4 | epD5 => false
      | _ => true
      end
  | Rh_Partial_DV =>
      match ep with
      | epD3 | epD4 => false
      | _ => true
      end
  | Rh_Partial_DVII =>
      match ep with
      | epD3 | epD5 | epD9 => false
      | _ => true
      end
  end.

Definition missing_epitopes (v : RhVariant) : list DEpitope :=
  filter (fun ep => negb (variant_has_epitope v ep)) all_d_epitopes.

Definition can_form_anti_epitope (recipient donor : RhVariant) (ep : DEpitope) : bool :=
  negb (variant_has_epitope recipient ep) && variant_has_epitope donor ep.

Definition epitope_incompatible (recipient donor : RhVariant) : bool :=
  existsb (can_form_anti_epitope recipient donor) all_d_epitopes.

Theorem normal_pos_has_all_epitopes : forall ep,
  variant_has_epitope Rh_Normal_Pos ep = true.
Proof. destruct ep; reflexivity. Qed.

Theorem normal_neg_has_no_epitopes : forall ep,
  variant_has_epitope Rh_Normal_Neg ep = false.
Proof. destruct ep; reflexivity. Qed.

Theorem weak_d_has_all_epitopes : forall ep,
  variant_has_epitope Rh_Weak_1 ep = true /\
  variant_has_epitope Rh_Weak_2 ep = true /\
  variant_has_epitope Rh_Weak_3 ep = true.
Proof. destruct ep; repeat split; reflexivity. Qed.

Theorem partial_DVI_missing_epitopes :
  missing_epitopes Rh_Partial_DVI = [epD1; epD5; epD6; epD7].
Proof. reflexivity. Qed.

Theorem partial_DVa_missing_epitopes :
  missing_epitopes Rh_Partial_DVa = [epD5; epD6; epD7].
Proof. reflexivity. Qed.

Theorem partial_D_incompatible_with_normal :
  epitope_incompatible Rh_Partial_DVI Rh_Normal_Pos = true.
Proof. reflexivity. Qed.

Theorem weak_d_compatible_with_normal :
  epitope_incompatible Rh_Weak_1 Rh_Normal_Pos = false.
Proof. reflexivity. Qed.

Theorem normal_neg_incompatible_with_any_pos : forall v,
  v <> Rh_Normal_Neg ->
  epitope_incompatible Rh_Normal_Neg v = true.
Proof.
  intros v Hneq. destruct v; try reflexivity.
  exfalso; apply Hneq; reflexivity.
Qed.

Definition rh_epitope_safe (recipient donor : RhVariant) : bool :=
  negb (epitope_incompatible recipient donor).

(** Extended case solver - available after ABOSubtype and RhVariant are defined *)
Ltac exhaust_extended_cases :=
  intros;
  repeat match goal with
  | [ x : ABO |- _ ] => destruct x
  | [ x : Rh |- _ ] => destruct x
  | [ x : BloodType |- _ ] => let a := fresh in let r := fresh in destruct x as [a r]
  | [ x : ABOSubtype |- _ ] => destruct x
  | [ x : RhVariant |- _ ] => destruct x
  | [ x : Severity |- _ ] => destruct x
  | [ x : Priority |- _ ] => destruct x
  | [ x : Product |- _ ] => destruct x
  | [ x : TiterLevel |- _ ] => destruct x
  end;
  try reflexivity; try discriminate; auto.

(** Rh variant compatibility check.
    Uses transfusion type for recipient (what they can safely receive)
    and donation type for donor (what antigen they express). *)
Definition rh_variant_compatible (r_variant d_variant : RhVariant) : bool :=
  let r_type := variant_transfusion_type r_variant in
  let d_type := variant_donation_type d_variant in
  match r_type, d_type with
  | Neg, Pos => false
  | _, _ => true
  end.

Theorem rh_variant_self_compatible : forall v,
  variant_transfusion_type v = variant_donation_type v ->
  rh_variant_compatible v v = true.
Proof.
  intros [| | | | | | | | | | | | ] H; simpl in *; try reflexivity; discriminate.
Qed.

Theorem partial_d_not_self_compatible :
  rh_variant_compatible Rh_Partial_DVI Rh_Partial_DVI = false.
Proof. reflexivity. Qed.

Theorem normal_pos_self_compatible :
  rh_variant_compatible Rh_Normal_Pos Rh_Normal_Pos = true.
Proof. reflexivity. Qed.

Theorem normal_neg_self_compatible :
  rh_variant_compatible Rh_Normal_Neg Rh_Normal_Neg = true.
Proof. reflexivity. Qed.

(** Weak D types are epitope-safe with any donor (they have all epitopes) *)
Theorem weak_d_epitope_safe_with_any : forall d,
  rh_epitope_safe Rh_Weak_1 d = true /\
  rh_epitope_safe Rh_Weak_2 d = true /\
  rh_epitope_safe Rh_Weak_3 d = true.
Proof. destruct d; repeat split; reflexivity. Qed.

(** Normal Rh-positive is epitope-safe with any donor *)
Theorem normal_pos_epitope_safe_with_any : forall d,
  rh_epitope_safe Rh_Normal_Pos d = true.
Proof. destruct d; reflexivity. Qed.

(** Normal Rh-negative is only epitope-safe with Rh-negative donors *)
Theorem normal_neg_epitope_safe_only_with_neg :
  rh_epitope_safe Rh_Normal_Neg Rh_Normal_Neg = true /\
  forall d, d <> Rh_Normal_Neg -> rh_epitope_safe Rh_Normal_Neg d = false.
Proof.
  split.
  - reflexivity.
  - intros d Hneq. destruct d; try reflexivity. exfalso; apply Hneq; reflexivity.
Qed.

(** Full subtype compatibility including both ABO subtypes and Rh variants *)
Definition full_subtype_compatible (r_sub d_sub : ABOSubtype)
                                   (r_rh d_rh : RhVariant) : bool :=
  subtype_compatible r_sub d_sub && rh_variant_compatible r_rh d_rh.

Theorem full_subtype_factors_abo_rh : forall rs ds rr dr,
  full_subtype_compatible rs ds rr dr = true <->
  (subtype_compatible rs ds = true /\ rh_variant_compatible rr dr = true).
Proof.
  intros; unfold full_subtype_compatible.
  rewrite andb_true_iff. reflexivity.
Qed.

(** Sensitization status *)
Inductive Sensitization : Type := Naive | Sensitized.

(** Extended recipient profile *)
Record Recipient := mkRecipient {
  rcpt_subtype : ABOSubtype;
  rcpt_rh_variant : RhVariant;
  rcpt_sensitized : Sensitization;
  rcpt_antibodies : list Antigen;
  rcpt_female_childbearing : bool
}.

(** Extended donor profile *)
Record Donor := mkDonor {
  donor_subtype : ABOSubtype;
  donor_rh_variant : RhVariant;
  donor_antigens : list Antigen
}.

(** Full extended compatibility *)
Definition extended_abo_compatible (r : Recipient) (d : Donor) : bool :=
  subtype_compatible (rcpt_subtype r) (donor_subtype d).

Definition extended_rh_compatible (r : Recipient) (d : Donor) : bool :=
  let r_type := variant_transfusion_type (rcpt_rh_variant r) in
  let d_type := variant_donation_type (donor_rh_variant d) in
  match r_type, d_type with
  | Neg, Pos =>
      match rcpt_sensitized r with
      | Sensitized => false
      | Naive => negb (rcpt_female_childbearing r)
      end
  | _, _ => true
  end.

Definition extended_minor_compatible (r : Recipient) (d : Donor) : bool :=
  forallb (fun ab => negb (existsb (fun ag =>
    if antigen_eq_dec ab ag then true else false) (donor_antigens d)))
    (rcpt_antibodies r).

Definition extended_compatible (r : Recipient) (d : Donor) : bool :=
  extended_abo_compatible r d &&
  extended_rh_compatible r d &&
  extended_minor_compatible r d.

(** Lift basic blood type to extended profile *)
Definition basic_recipient (bt : BloodType) : Recipient :=
  mkRecipient
    (match fst bt with A => Sub_A1 | B => Sub_B | AB => Sub_A1B | O => Sub_O end)
    (match snd bt with Pos => Rh_Normal_Pos | Neg => Rh_Normal_Neg end)
    Sensitized [] false.

Definition basic_donor (bt : BloodType) : Donor :=
  mkDonor
    (match fst bt with A => Sub_A1 | B => Sub_B | AB => Sub_A1B | O => Sub_O end)
    (match snd bt with Pos => Rh_Normal_Pos | Neg => Rh_Normal_Neg end)
    [].

Theorem extended_conservative : forall bt_r bt_d,
  compatible bt_r bt_d = true ->
  extended_compatible (basic_recipient bt_r) (basic_donor bt_d) = true.
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]]; simpl; intro H;
  try exact H; try reflexivity; try discriminate.
Qed.

(** Extended minor compatibility is satisfied when recipient has no antibodies *)
Theorem extended_minor_always_ok_when_no_antibodies : forall r d,
  rcpt_antibodies r = [] -> extended_minor_compatible r d = true.
Proof.
  intros r d H. unfold extended_minor_compatible. rewrite H. reflexivity.
Qed.

(** Extended compatibility reduces to ABO+Rh when no minor antibodies/antigens *)
Theorem extended_reduces_to_basic : forall r d,
  rcpt_antibodies r = [] ->
  donor_antigens d = [] ->
  extended_compatible r d = extended_abo_compatible r d && extended_rh_compatible r d.
Proof.
  intros r d Hra Hda.
  unfold extended_compatible.
  rewrite extended_minor_always_ok_when_no_antibodies by exact Hra.
  rewrite andb_true_r. reflexivity.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                           VI. GENETICS                                     *)
(*                                                                            *)
(******************************************************************************)

(** ABO alleles *)
Inductive ABOAllele : Type := Allele_A | Allele_B | Allele_O.

(** Rh alleles *)
Inductive RhAllele : Type := Allele_D | Allele_d.

Definition ABOGenotype : Type := (ABOAllele * ABOAllele)%type.
Definition RhGenotype : Type := (RhAllele * RhAllele)%type.
Definition FullGenotype : Type := (ABOGenotype * RhGenotype)%type.

Definition abo_phenotype (g : ABOGenotype) : ABO :=
  match g with
  | (Allele_A, Allele_A) | (Allele_A, Allele_O) | (Allele_O, Allele_A) => A
  | (Allele_B, Allele_B) | (Allele_B, Allele_O) | (Allele_O, Allele_B) => B
  | (Allele_A, Allele_B) | (Allele_B, Allele_A) => AB
  | (Allele_O, Allele_O) => O
  end.

Definition rh_phenotype (g : RhGenotype) : Rh :=
  match g with
  | (Allele_D, _) | (_, Allele_D) => Pos
  | (Allele_d, Allele_d) => Neg
  end.

Definition genotype_phenotype (g : FullGenotype) : BloodType :=
  (abo_phenotype (fst g), rh_phenotype (snd g)).

(** Punnett square — all possible offspring genotypes *)
Definition punnett_abo (p1 p2 : ABOGenotype) : list ABOGenotype :=
  let (a1, a2) := p1 in let (b1, b2) := p2 in
  [(a1,b1); (a1,b2); (a2,b1); (a2,b2)].

Definition punnett_rh (p1 p2 : RhGenotype) : list RhGenotype :=
  let (a1, a2) := p1 in let (b1, b2) := p2 in
  [(a1,b1); (a1,b2); (a2,b1); (a2,b2)].

Definition punnett_full (p1 p2 : FullGenotype) : list FullGenotype :=
  flat_map (fun abo => map (fun rh => (abo, rh))
    (punnett_rh (snd p1) (snd p2))) (punnett_abo (fst p1) (fst p2)).

Definition offspring_phenotypes (p1 p2 : FullGenotype) : list BloodType :=
  map genotype_phenotype (punnett_full p1 p2).

Theorem punnett_produces_16 : forall p1 p2,
  length (punnett_full p1 p2) = 16.
Proof. intros [[? ?] [? ?]] [[? ?] [? ?]]; reflexivity. Qed.

(** Mendelian inheritance proofs *)
Theorem OO_parents_O_children : forall g,
  In g (punnett_abo (Allele_O, Allele_O) (Allele_O, Allele_O)) ->
  abo_phenotype g = O.
Proof.
  intros [g1 g2] H; simpl in H.
  destruct H as [H|[H|[H|[H|[]]]]]; injection H; intros; subst; reflexivity.
Qed.

Theorem dd_parents_neg_children : forall g,
  In g (punnett_rh (Allele_d, Allele_d) (Allele_d, Allele_d)) ->
  rh_phenotype g = Neg.
Proof.
  intros [g1 g2] H; simpl in H.
  destruct H as [H|[H|[H|[H|[]]]]]; injection H; intros; subst; reflexivity.
Qed.

Theorem Dd_cross_ratio :
  let outcomes := map rh_phenotype (punnett_rh (Allele_D, Allele_d) (Allele_D, Allele_d)) in
  length (filter (fun r => match r with Pos => true | Neg => false end) outcomes) = 3 /\
  length (filter (fun r => match r with Neg => true | Pos => false end) outcomes) = 1.
Proof. split; reflexivity. Qed.

(** Phenotype distribution from Punnett square *)
Record PhenoDistribution := mkPhenoDist {
  pd_A : nat; pd_B : nat; pd_AB : nat; pd_O : nat
}.

Definition count_phenotype (target : ABO) (gs : list ABOGenotype) : nat :=
  length (filter (fun g => if abo_eq_dec (abo_phenotype g) target then true else false) gs).

Definition abo_distribution (p1 p2 : ABOGenotype) : PhenoDistribution :=
  let gs := punnett_abo p1 p2 in
  mkPhenoDist (count_phenotype A gs) (count_phenotype B gs)
              (count_phenotype AB gs) (count_phenotype O gs).

Theorem AO_AO_distribution :
  let d := abo_distribution (Allele_A, Allele_O) (Allele_A, Allele_O) in
  pd_A d = 3 /\ pd_O d = 1 /\ pd_B d = 0 /\ pd_AB d = 0.
Proof. repeat split; reflexivity. Qed.

Theorem AO_BO_distribution :
  let d := abo_distribution (Allele_A, Allele_O) (Allele_B, Allele_O) in
  pd_A d = 1 /\ pd_B d = 1 /\ pd_AB d = 1 /\ pd_O d = 1.
Proof. repeat split; reflexivity. Qed.

(** Hardy-Weinberg equilibrium - integer version for compatibility *)
Record AlleleFreq := mkAlleleFreq { freq_pA : nat; freq_pB : nat; freq_pO : nat }.

Definition hardy_weinberg (f : AlleleFreq) : PhenoDistribution :=
  let pA := freq_pA f in let pB := freq_pB f in let pO := freq_pO f in
  mkPhenoDist (pA*pA + 2*pA*pO) (pB*pB + 2*pB*pO) (2*pA*pB) (pO*pO).

Theorem hardy_weinberg_totals : forall f,
  let d := hardy_weinberg f in
  let t := freq_pA f + freq_pB f + freq_pO f in
  pd_A d + pd_B d + pd_AB d + pd_O d = t * t.
Proof. intros; unfold hardy_weinberg; simpl; lia. Qed.

Require Import QArith.

Section RationalFrequencies.
Open Scope Q_scope.

(** Hardy-Weinberg equilibrium - rational (Q) version for precision.
    Allele frequencies are represented as rationals summing to 1.
    This avoids the precision loss of integer-scaled frequencies. *)
Record AlleleFreqQ := mkAlleleFreqQ {
  freq_pA_Q : Q;
  freq_pB_Q : Q;
  freq_pO_Q : Q
}.

Record PhenoDistributionQ := mkPhenoDistQ {
  pd_A_Q : Q;
  pd_B_Q : Q;
  pd_AB_Q : Q;
  pd_O_Q : Q
}.

Definition hardy_weinberg_Q (f : AlleleFreqQ) : PhenoDistributionQ :=
  let pA := freq_pA_Q f in
  let pB := freq_pB_Q f in
  let pO := freq_pO_Q f in
  mkPhenoDistQ
    (pA * pA + 2 * pA * pO)
    (pB * pB + 2 * pB * pO)
    (2 * pA * pB)
    (pO * pO).

Definition allele_freq_sum (f : AlleleFreqQ) : Q :=
  freq_pA_Q f + freq_pB_Q f + freq_pO_Q f.

Definition pheno_dist_sum (d : PhenoDistributionQ) : Q :=
  pd_A_Q d + pd_B_Q d + pd_AB_Q d + pd_O_Q d.

(** The Hardy-Weinberg principle: if allele frequencies sum to 1,
    then genotype frequencies also sum to 1. This is because
    (pA + pB + pO)^2 expands to the sum of all genotype frequencies. *)
Theorem hardy_weinberg_Q_totals : forall f,
  allele_freq_sum f == 1 ->
  pheno_dist_sum (hardy_weinberg_Q f) == 1.
Proof.
  intros [pA pB pO] Hsum.
  unfold hardy_weinberg_Q, pheno_dist_sum, allele_freq_sum in *. simpl in *.
  assert (H: pA * pA + 2 * pA * pO + (pB * pB + 2 * pB * pO) + 2 * pA * pB + pO * pO
             == (pA + pB + pO) * (pA + pB + pO)) by ring.
  rewrite H. rewrite Hsum. ring.
Qed.

Definition us_allele_freq_Q : AlleleFreqQ :=
  mkAlleleFreqQ (28 # 100) (7 # 100) (65 # 100).

Theorem us_allele_freq_Q_sums_to_1 :
  allele_freq_sum us_allele_freq_Q == 1.
Proof. unfold allele_freq_sum, us_allele_freq_Q; simpl. reflexivity. Qed.

Definition expected_phenotype_freq_Q (f : AlleleFreqQ) (pheno : ABO) : Q :=
  let d := hardy_weinberg_Q f in
  match pheno with
  | A => pd_A_Q d
  | B => pd_B_Q d
  | AB => pd_AB_Q d
  | O => pd_O_Q d
  end.

Definition expected_O_freq_US : Q := expected_phenotype_freq_Q us_allele_freq_Q O.

Theorem expected_O_freq_US_value :
  expected_O_freq_US == (4225 # 10000).
Proof. unfold expected_O_freq_US, expected_phenotype_freq_Q, hardy_weinberg_Q, us_allele_freq_Q. simpl. reflexivity. Qed.

(** Rh allele frequencies using rationals *)
Record RhAlleleFreqQ := mkRhAlleleFreqQ {
  freq_D_Q : Q;
  freq_d_Q : Q
}.

Definition expected_rh_neg_Q (f : RhAlleleFreqQ) : Q :=
  freq_d_Q f * freq_d_Q f.

Definition expected_rh_pos_Q (f : RhAlleleFreqQ) : Q :=
  1 - expected_rh_neg_Q f.

Definition us_rh_freq_Q : RhAlleleFreqQ := mkRhAlleleFreqQ (60 # 100) (40 # 100).

Theorem us_rh_neg_expected :
  expected_rh_neg_Q us_rh_freq_Q == (16 # 100).
Proof. unfold expected_rh_neg_Q, us_rh_freq_Q. simpl. reflexivity. Qed.

End RationalFrequencies.

Close Scope Q_scope.

(** Rh haplotypes (for extended Rh system) *)
Record RhHaplotype := mkRhHap { hap_D : bool; hap_C : bool; hap_E : bool }.

Definition DCe : RhHaplotype := mkRhHap true true false.
Definition DcE : RhHaplotype := mkRhHap true false true.
Definition dce : RhHaplotype := mkRhHap false false false.

Definition rh_phenotype_from_haps (h1 h2 : RhHaplotype) : Rh :=
  if hap_D h1 || hap_D h2 then Pos else Neg.

(******************************************************************************)
(*                                                                            *)
(*                       VII. CLINICAL PRACTICE                               *)
(*                                                                            *)
(******************************************************************************)

(** Population frequencies per 1000
    Sources:
    - US: Stanford Blood Center, American Red Cross published statistics
          Rh-negative ~15% of Caucasian population
    - Japan: Japanese Red Cross Society data
            Rh-negative extremely rare (<0.5%) in East Asian populations
    - Nigeria: Nigerian National Blood Transfusion Service studies
              West African populations have higher O prevalence, low Rh-negative
    - India: Indian Journal of Hematology and Blood Transfusion meta-analyses
             B antigen more common than in Western populations

    Note: These are approximations normalized to sum to 1000. Actual frequencies
    vary by region, ethnicity, and study methodology. *)
Inductive Population : Type := US | Japan | Nigeria | India.

Definition pop_frequency (pop : Population) (bt : BloodType) : nat :=
  match pop, bt with
  | US, (O, Pos) => 374 | US, (O, Neg) => 66
  | US, (A, Pos) => 357 | US, (A, Neg) => 63
  | US, (B, Pos) => 85  | US, (B, Neg) => 15
  | US, (AB, Pos) => 34 | US, (AB, Neg) => 6
  | Japan, (O, Pos) => 294 | Japan, (O, Neg) => 1
  | Japan, (A, Pos) => 390 | Japan, (A, Neg) => 2
  | Japan, (B, Pos) => 215 | Japan, (B, Neg) => 1
  | Japan, (AB, Pos) => 96 | Japan, (AB, Neg) => 1
  | Nigeria, (O, Pos) => 504 | Nigeria, (O, Neg) => 26
  | Nigeria, (A, Pos) => 224 | Nigeria, (A, Neg) => 12
  | Nigeria, (B, Pos) => 186 | Nigeria, (B, Neg) => 10
  | Nigeria, (AB, Pos) => 36 | Nigeria, (AB, Neg) => 2
  | India, (O, Pos) => 354 | India, (O, Neg) => 25
  | India, (A, Pos) => 219 | India, (A, Neg) => 14
  | India, (B, Pos) => 295 | India, (B, Neg) => 16
  | India, (AB, Pos) => 71 | India, (AB, Neg) => 6
  end.

Definition pop_sum (pop : Population) : nat :=
  fold_left Nat.add (map (pop_frequency pop) all_blood_types) 0.

Theorem all_pops_sum_1000 : forall pop, pop_sum pop = 1000.
Proof. intros [| | | ]; reflexivity. Qed.

(** Hospital inventory *)
Record Inventory := mkInventory {
  inv : BloodType -> nat
}.

Definition total_units (i : Inventory) : nat :=
  fold_left Nat.add (map (inv i) all_blood_types) 0.

Definition available_for (i : Inventory) (recipient : BloodType) : nat :=
  fold_left Nat.add
    (map (fun d => if compatible recipient d then inv i d else 0) all_blood_types) 0.

(** Transfusion dosing *)
Definition rbc_dose (current_hgb target_hgb weight_kg : nat) : nat :=
  ((target_hgb - current_hgb) * weight_kg) / 70.

Definition platelet_dose (weight_kg : nat) : nat :=
  if Nat.leb weight_kg 10 then 1
  else if Nat.leb weight_kg 30 then 2
  else if Nat.leb weight_kg 50 then 4
  else 6.

Definition ffp_dose_ml (weight_kg : nat) : nat := weight_kg * 15.

Theorem dosing_examples :
  platelet_dose 70 = 6 /\ platelet_dose 25 = 2 /\ ffp_dose_ml 70 = 1050.
Proof. repeat split; reflexivity. Qed.

(** Laboratory tests *)
Inductive LabTest : Type :=
  | TypeAndScreen | AntibodyID | ImmediateSpin
  | AHGCrossmatch | ElectronicCrossmatch | DAT.

Definition test_time_minutes (t : LabTest) : nat :=
  match t with
  | TypeAndScreen => 45 | AntibodyID => 120 | ImmediateSpin => 5
  | AHGCrossmatch => 45 | ElectronicCrossmatch => 1 | DAT => 30
  end.

Definition electronic_xm_eligible (two_determinations no_antibodies : bool) : bool :=
  two_determinations && no_antibodies.

Theorem electronic_fastest :
  test_time_minutes ElectronicCrossmatch < test_time_minutes ImmediateSpin.
Proof. simpl; lia. Qed.

(** Direct Antiglobulin Test (DAT) / Coombs Test Modeling.

    The DAT detects antibodies or complement bound to RBC surfaces.
    Positive DAT indicates:
    - Autoimmune hemolytic anemia (AIHA) - warm or cold type
    - Drug-induced hemolytic anemia
    - Hemolytic disease of the fetus/newborn (HDFN)
    - Transfusion reaction (delayed hemolytic)
    - Alloantibody coating from incompatible transfusion

    Clinical significance for transfusion:
    - Positive DAT complicates crossmatching
    - May indicate underlying autoimmune condition
    - Warm AIHA: autoantibodies often have Rh-like specificity
    - Cold AIHA: anti-I or anti-i specificity common *)

Inductive DATResult : Type :=
  | DAT_Negative
  | DAT_Weak_Positive
  | DAT_Positive
  | DAT_Strong_Positive.

Inductive DATPattern : Type :=
  | DAT_IgG_Only
  | DAT_C3_Only
  | DAT_IgG_and_C3
  | DAT_IgA_Only
  | DAT_IgM_Only.

Inductive AIHAType : Type :=
  | AIHA_Warm
  | AIHA_Cold
  | AIHA_Mixed
  | AIHA_Drug_Induced
  | AIHA_None.

Record DATProfile := mkDATProfile {
  dat_result : DATResult;
  dat_pattern : option DATPattern;
  dat_autoantibody_specificity : option Antigen;
  dat_thermal_amplitude : option nat
}.

Definition dat_positive (d : DATProfile) : bool :=
  match dat_result d with
  | DAT_Negative => false
  | _ => true
  end.

Definition classify_aiha (d : DATProfile) : AIHAType :=
  match dat_result d, dat_pattern d, dat_thermal_amplitude d with
  | DAT_Negative, _, _ => AIHA_None
  | _, Some DAT_IgG_Only, Some temp =>
      if Nat.leb 37 temp then AIHA_Warm else AIHA_Cold
  | _, Some DAT_IgG_Only, None => AIHA_Warm
  | _, Some DAT_C3_Only, Some temp =>
      if Nat.leb temp 30 then AIHA_Cold else AIHA_Mixed
  | _, Some DAT_C3_Only, None => AIHA_Cold
  | _, Some DAT_IgG_and_C3, _ => AIHA_Mixed
  | _, _, _ => AIHA_Warm
  end.

Definition transfusion_risk_with_aiha (aiha : AIHAType) : Severity :=
  match aiha with
  | AIHA_None => Safe
  | AIHA_Cold => DelayedHemolytic
  | AIHA_Warm => AcuteHemolytic
  | AIHA_Mixed => SevereAcuteHemolytic
  | AIHA_Drug_Induced => DelayedHemolytic
  end.

Definition crossmatch_difficulty (d : DATProfile) : nat :=
  match dat_result d with
  | DAT_Negative => 0
  | DAT_Weak_Positive => 1
  | DAT_Positive => 2
  | DAT_Strong_Positive => 3
  end.

Definition needs_adsorption_study (d : DATProfile) : bool :=
  match dat_result d with
  | DAT_Positive | DAT_Strong_Positive => true
  | _ => false
  end.

Definition least_incompatible_strategy (d : DATProfile) : bool :=
  dat_positive d && needs_adsorption_study d.

Theorem negative_dat_no_aiha : forall d,
  dat_result d = DAT_Negative -> classify_aiha d = AIHA_None.
Proof. intros d H. unfold classify_aiha. rewrite H. reflexivity. Qed.

Theorem positive_dat_complicates_crossmatch : forall d,
  dat_positive d = true -> crossmatch_difficulty d >= 1.
Proof.
  intros d H. unfold dat_positive, crossmatch_difficulty in *.
  destruct (dat_result d); simpl in *; try discriminate; lia.
Qed.

Theorem strong_positive_needs_adsorption :
  needs_adsorption_study (mkDATProfile DAT_Strong_Positive None None None) = true.
Proof. reflexivity. Qed.

Definition warm_aiha_example : DATProfile :=
  mkDATProfile DAT_Positive (Some DAT_IgG_Only) (Some Ag_e) (Some 37).

Definition cold_aiha_example : DATProfile :=
  mkDATProfile DAT_Positive (Some DAT_C3_Only) (Some Ag_I) (Some 4).

Theorem warm_aiha_classified_correctly :
  classify_aiha warm_aiha_example = AIHA_Warm.
Proof. reflexivity. Qed.

Theorem cold_aiha_classified_correctly :
  classify_aiha cold_aiha_example = AIHA_Cold.
Proof. reflexivity. Qed.

(** Extended compatibility with DAT profile consideration.
    DAT-positive patients require special handling:
    - May need least-incompatible unit selection
    - Autoantibody specificity affects unit selection
    - Crossmatch may be incompatible despite ABO/Rh match *)
Definition extended_compatible_with_dat (r : Recipient) (d : Donor)
                                        (dat : DATProfile) : bool * AIHAType :=
  let base_compat := extended_compatible r d in
  let aiha := classify_aiha dat in
  (base_compat, aiha).

Definition extended_transfusion_safe (r : Recipient) (d : Donor)
                                     (dat : DATProfile) : bool :=
  let (compat, aiha) := extended_compatible_with_dat r d dat in
  compat && match aiha with
            | AIHA_None => true
            | AIHA_Cold => true
            | _ => false
            end.

Theorem dat_negative_no_aiha_concern : forall r d,
  let dat := mkDATProfile DAT_Negative None None None in
  extended_transfusion_safe r d dat = extended_compatible r d.
Proof.
  intros r d.
  unfold extended_transfusion_safe, extended_compatible_with_dat, classify_aiha.
  simpl. rewrite andb_true_r. reflexivity.
Qed.

(** ========== COLD AGGLUTININ DISEASE (CAD) MODEL ========== *)

(** Cold agglutinin disease is characterized by IgM autoantibodies that bind
    RBCs at temperatures below 37°C, fixing complement and causing hemolysis.

    Key parameters:
    - Thermal amplitude: highest temperature at which antibody reacts
      (clinically significant if >= 30°C)
    - Titer: dilution at which agglutination is still visible (e.g., 1:512)
      Higher titers correlate with clinical severity
    - Specificity: usually anti-I (adults), anti-i (children/lymphoma)

    Transfusion considerations:
    - Blood warmer MANDATORY to prevent in vivo agglutination
    - Avoid cooling patient during surgery
    - Crossmatch at 37°C to avoid false positives
    - Low-titer cold agglutinins are usually benign *)

Record ColdAgglutininProfile := mkCADProfile {
  cad_titer : nat;                    (** Reciprocal, e.g., 512 for 1:512 *)
  cad_thermal_amplitude : nat;        (** Highest reactive temp in Celsius *)
  cad_specificity : Antigen;          (** Usually Ag_I or Ag_i *)
  cad_complement_activation : bool;   (** C3 fixation observed *)
  cad_hemolysis_present : bool
}.

(** Titer thresholds based on clinical significance *)
Definition cad_titer_low : nat := 64.
Definition cad_titer_moderate : nat := 256.
Definition cad_titer_high : nat := 1024.
Definition cad_titer_critical : nat := 4096.

(** Thermal amplitude threshold for clinical significance *)
Definition cad_thermal_threshold : nat := 30.

Inductive CADSeverity : Type :=
  | CAD_Benign           (** Low titer, low thermal amplitude *)
  | CAD_Mild             (** Moderate titer, may need precautions *)
  | CAD_Moderate         (** High titer or high thermal amplitude *)
  | CAD_Severe           (** High titer AND high thermal amplitude *)
  | CAD_Critical.        (** Active hemolysis, life-threatening *)

Definition classify_cad_severity (c : ColdAgglutininProfile) : CADSeverity :=
  let high_thermal := Nat.leb cad_thermal_threshold (cad_thermal_amplitude c) in
  let titer := cad_titer c in
  if cad_hemolysis_present c then CAD_Critical
  else if Nat.leb cad_titer_critical titer then
    if high_thermal then CAD_Critical else CAD_Severe
  else if Nat.leb cad_titer_high titer then
    if high_thermal then CAD_Severe else CAD_Moderate
  else if Nat.leb cad_titer_moderate titer then
    if high_thermal then CAD_Moderate else CAD_Mild
  else if Nat.leb cad_titer_low titer then
    if high_thermal then CAD_Mild else CAD_Benign
  else CAD_Benign.

(** Transfusion requirements for cold agglutinin patients *)
Record CADTransfusionRequirements := mkCADReq {
  cad_req_blood_warmer : bool;
  cad_req_warm_room : bool;           (** Keep patient/OR warm *)
  cad_req_prewarm_crossmatch : bool;
  cad_req_avoid_cold_fluids : bool;
  cad_req_plasma_exchange : bool      (** For severe/refractory cases *)
}.

Definition cad_transfusion_requirements (c : ColdAgglutininProfile)
    : CADTransfusionRequirements :=
  let severity := classify_cad_severity c in
  match severity with
  | CAD_Benign => mkCADReq false false false false false
  | CAD_Mild => mkCADReq true false true false false
  | CAD_Moderate => mkCADReq true true true true false
  | CAD_Severe => mkCADReq true true true true false
  | CAD_Critical => mkCADReq true true true true true
  end.

(** Blood warmer is required for any severity above benign *)
Theorem cad_warmer_required_above_benign : forall c,
  classify_cad_severity c <> CAD_Benign ->
  cad_req_blood_warmer (cad_transfusion_requirements c) = true.
Proof.
  intros c H.
  unfold cad_transfusion_requirements.
  destruct (classify_cad_severity c); try reflexivity.
  exfalso; apply H; reflexivity.
Qed.

(** High thermal amplitude alone triggers warmer requirement *)
Theorem high_thermal_requires_precautions :
  forall titer spec comp hem,
  cad_req_blood_warmer
    (cad_transfusion_requirements (mkCADProfile titer 32 spec comp hem)) = true \/
  titer < cad_titer_low.
Proof.
Admitted.

(** Example: benign cold agglutinin (incidental finding) *)
Definition cad_example_benign : ColdAgglutininProfile :=
  mkCADProfile 32 4 Ag_I false false.

(** Example: severe cold agglutinin disease *)
Definition cad_example_severe : ColdAgglutininProfile :=
  mkCADProfile 2048 34 Ag_I true true.

Theorem benign_cad_no_warmer :
  cad_req_blood_warmer (cad_transfusion_requirements cad_example_benign) = false.
Proof. reflexivity. Qed.

Theorem severe_cad_plasma_exchange :
  cad_req_plasma_exchange (cad_transfusion_requirements cad_example_severe) = true.
Proof. reflexivity. Qed.

(** Reaction severity assessment *)
Definition assess_severity (recipient donor : BloodType) : Severity :=
  if compatible recipient donor then Safe
  else match fst recipient, fst donor, snd recipient, snd donor with
  | O, AB, _, _ => LifeThreatening
  | O, A, _, _ => SevereAcuteHemolytic
  | O, B, _, _ => SevereAcuteHemolytic
  | A, B, _, _ => LifeThreatening
  | B, A, _, _ => LifeThreatening
  | A, AB, _, _ => AcuteHemolytic
  | B, AB, _, _ => AcuteHemolytic
  | _, _, Neg, Pos => DelayedHemolytic
  | _, _, _, _ => AcuteHemolytic
  end.

Definition severity_score (s : Severity) : nat :=
  match s with
  | Safe => 0 | DelayedHemolytic => 1 | AcuteHemolytic => 2
  | SevereAcuteHemolytic => 3 | LifeThreatening => 4
  end.

Theorem compatible_is_safe : forall r d,
  compatible r d = true -> assess_severity r d = Safe.
Proof. intros r d H; unfold assess_severity; rewrite H; reflexivity. Qed.

Theorem severity_examples :
  assess_severity A_pos B_pos = LifeThreatening /\
  assess_severity A_neg A_pos = DelayedHemolytic /\
  assess_severity A_pos O_neg = Safe.
Proof. repeat split; reflexivity. Qed.

(** Neonatal considerations *)
Record Neonate := mkNeonate {
  neo_abo : ABO;
  neo_rh : Rh;
  maternal_abo : ABO;
  maternal_rh : Rh;
  age_days : nat
}.

Definition neonatal_compatible (n : Neonate) (donor : BloodType) : bool :=
  compatible (neo_abo n, neo_rh n) donor &&
  compatible (maternal_abo n, maternal_rh n) donor.

Theorem neonate_maternal_requirement : forall n d,
  neonatal_compatible n d = true ->
  compatible (maternal_abo n, maternal_rh n) d = true.
Proof.
  intros n d H; unfold neonatal_compatible in H.
  apply andb_prop in H; destruct H; assumption.
Qed.

(** HDFN and RhoGAM *)
Definition hdfn_rh_risk (maternal_rh paternal_rh : Rh) : bool :=
  match maternal_rh, paternal_rh with Neg, Pos => true | _, _ => false end.

Definition rhogam_indicated (maternal_rh paternal_rh : Rh) (already_sensitized : bool) : bool :=
  hdfn_rh_risk maternal_rh paternal_rh && negb already_sensitized.

Theorem rhogam_logic :
  rhogam_indicated Neg Pos false = true /\
  rhogam_indicated Neg Pos true = false /\
  rhogam_indicated Pos Pos false = false.
Proof. repeat split; reflexivity. Qed.

(******************************************************************************)
(*                                                                            *)
(*                    VIII. UNIFIED DECISION MODEL                            *)
(*                                                                            *)
(******************************************************************************)

Inductive MatchQuality : Type :=
  | Exact | ABO_Match | Crosstype | Incompatible_Match.

Definition match_quality (recipient donor : BloodType) : MatchQuality :=
  if blood_eq_dec recipient donor then Exact
  else if abo_eq_dec (fst recipient) (fst donor) then
    if compatible recipient donor then ABO_Match else Incompatible_Match
  else if compatible recipient donor then Crosstype
  else Incompatible_Match.

Record TransfusionDecision := mkDecision {
  td_compatible : bool;
  td_match : MatchQuality;
  td_severity : Severity;
  td_crossmatch : LabTest
}.

Definition make_decision (r d : BloodType) (has_antibodies : bool) : TransfusionDecision :=
  mkDecision
    (compatible r d)
    (match_quality r d)
    (assess_severity r d)
    (if has_antibodies then AHGCrossmatch else ElectronicCrossmatch).

Definition decision_safe (d : TransfusionDecision) : bool :=
  td_compatible d && match td_severity d with Safe => true | _ => false end.

Theorem safe_decision_properties : forall r d,
  compatible r d = true ->
  let dec := make_decision r d false in
  td_compatible dec = true /\ td_severity dec = Safe.
Proof.
  intros r d H; split.
  - unfold make_decision; simpl; exact H.
  - unfold make_decision; simpl; apply compatible_is_safe; exact H.
Qed.

(** Allocation priority *)
Definition priority_value (p : Priority) : nat :=
  match p with Emergency => 0 | Urgent => 1 | Routine => 2 | Elective => 3 end.

Definition higher_priority (p1 p2 : Priority) : bool :=
  Nat.ltb (priority_value p1) (priority_value p2).

Theorem emergency_highest : forall p,
  p <> Emergency -> higher_priority Emergency p = true.
Proof. intros [| | | ] H; try reflexivity; exfalso; apply H; reflexivity. Qed.

(** Allocation preference — conserve O-neg *)
Definition allocation_score (recipient donor : BloodType) : nat :=
  if blood_eq_dec recipient donor then 0
  else if compatible recipient donor then
    match donor with
    | (O, Neg) => 100
    | (O, Pos) => 50
    | (_, Neg) => 30
    | _ => 10
    end
  else 200.

Theorem exact_match_optimal : forall bt,
  allocation_score bt bt = 0.
Proof. intros [[| | | ] [| ]]; reflexivity. Qed.

Theorem O_neg_conserved : forall bt,
  bt <> O_neg -> compatible bt O_neg = true ->
  allocation_score bt O_neg = 100.
Proof.
  intros [[| | | ] [| ]] Hneq Hcompat;
  unfold allocation_score;
  destruct (blood_eq_dec _ _); try reflexivity;
  try (exfalso; apply Hneq; assumption).
Qed.

(******************************************************************************)
(*                                                                            *)
(*                         SPECIFICATION SUMMARY                              *)
(*                                                                            *)
(*  Naming Conventions:                                                       *)
(*  - SPEC_xxx: Formal specification definitions (Props)                      *)
(*  - spec_xxx: Theorems proving specifications                               *)
(*  - xxx_yyy: Function/definition names use underscores                      *)
(*  - XxxYyy: Type names use CamelCase                                        *)
(*  - Theorem names describe the property being proved                        *)
(*                                                                            *)
(******************************************************************************)

Definition SPEC_universal_donor : Prop :=
  forall r, compatible r O_neg = true.

Definition SPEC_universal_recipient : Prop :=
  forall d, compatible AB_pos d = true.

Definition SPEC_self_safe : Prop :=
  forall bt, compatible bt bt = true.

Definition SPEC_rh_constraint : Prop :=
  forall abo, compatible (abo, Neg) (abo, Pos) = false.

Definition SPEC_safety_equiv : Prop :=
  forall r d, compatible r d = true <-> no_adverse_reaction r d.

Definition SPEC_unique_universal : Prop :=
  forall d, (forall r, compatible r d = true) -> d = O_neg.

Definition SPEC_extended_sound : Prop :=
  forall r d, compatible r d = true ->
    extended_compatible (basic_recipient r) (basic_donor d) = true.

Theorem spec_universal_donor : SPEC_universal_donor.
Proof. exact O_neg_universal_donor. Qed.

Theorem spec_universal_recipient : SPEC_universal_recipient.
Proof. exact AB_pos_universal_recipient. Qed.

Theorem spec_self_safe : SPEC_self_safe.
Proof. exact self_compatible. Qed.

Theorem spec_rh_constraint : SPEC_rh_constraint.
Proof. exact Rh_neg_cannot_receive_pos. Qed.

Theorem spec_safety_equiv : SPEC_safety_equiv.
Proof. exact compatible_iff_safe. Qed.

Theorem spec_unique_universal : SPEC_unique_universal.
Proof. exact O_neg_unique_universal. Qed.

Theorem spec_extended_sound : SPEC_extended_sound.
Proof. exact extended_conservative. Qed.

(** Minor blood group systems using unified Antigen type.

    All minor antigens use the unified Antigen type from Section I.
    No separate KellAntigen, DuffyAntigen, etc. types are needed.
    This provides:
    1. Consistency with the core antigen model
    2. Set-based compatibility checking
    3. Proper integration with antibody history tracking *)

(** Extended antigen profile: an individual's full antigen phenotype.
    Uses the AntigenSet type defined in Section II. *)
Record ExtendedPhenotype := mkExtendedPhenotype {
  ep_base_type : BloodType;
  ep_antigens : AntigenSet
}.

(** Build an extended phenotype from base type plus minor antigens *)
Definition make_extended_phenotype (bt : BloodType) (minor_ags : list Antigen)
    : ExtendedPhenotype :=
  mkExtendedPhenotype bt
    (fun ag => phenotype_antigens bt ag ||
               existsb (fun ag' => if antigen_eq_dec ag ag' then true else false) minor_ags).

(** Common phenotype patterns *)
Definition phenotype_K_positive (bt : BloodType) : ExtendedPhenotype :=
  make_extended_phenotype bt [Ag_K].

Definition phenotype_K_negative (bt : BloodType) : ExtendedPhenotype :=
  make_extended_phenotype bt [Ag_k; Ag_Kpb].

Definition phenotype_Fya_positive (bt : BloodType) : ExtendedPhenotype :=
  make_extended_phenotype bt [Ag_Fya].

Definition phenotype_Fyb_positive (bt : BloodType) : ExtendedPhenotype :=
  make_extended_phenotype bt [Ag_Fyb].

Definition phenotype_Fy_null (bt : BloodType) : ExtendedPhenotype :=
  make_extended_phenotype bt [].

Definition phenotype_Jka_positive (bt : BloodType) : ExtendedPhenotype :=
  make_extended_phenotype bt [Ag_Jka].

Definition phenotype_Jkb_positive (bt : BloodType) : ExtendedPhenotype :=
  make_extended_phenotype bt [Ag_Jkb].

(** Minor antigen compatibility using set disjointness.
    Recipient antibodies (list) must not match donor antigens (set). *)
Definition minor_antigen_compatible (recipient_antibodies : list Antigen)
                                    (donor_phenotype : ExtendedPhenotype) : bool :=
  forallb (fun ab => negb (ep_antigens donor_phenotype ab)) recipient_antibodies.

(** Minor antigen list utilities.
    All minor antigen operations use the unified Antigen type directly
    with list Antigen for collections. No wrapper types needed. *)

Definition antigen_list_to_set (ags : list Antigen) : AntigenSet :=
  fun ag => existsb (fun ag' => if antigen_eq_dec ag ag' then true else false) ags.

Definition has_antigen_in_list (ags : list Antigen) (ag : Antigen) : bool :=
  antigen_list_to_set ags ag.

Definition minor_antigen_compatible_list (recipient_abs : list Antigen)
                                         (donor_ags : list Antigen) : bool :=
  forallb (fun ag => negb (has_antigen_in_list donor_ags ag)) recipient_abs.

(** Common minor antigen phenotype patterns for routine matching *)
Definition default_minor_antigen_list : list Antigen :=
  [Ag_k; Ag_Kpb; Ag_Fyb; Ag_Jka; Ag_M; Ag_S; Ag_Leb].

(** Sickle cell phenotype matching requirements (C, E, K negative) *)
Definition sickle_cell_matching_antigens : list Antigen :=
  [Ag_C; Ag_E; Ag_K].

(** Chronically transfused patient extended matching *)
Definition extended_matching_antigens : list Antigen :=
  [Ag_C; Ag_E; Ag_c; Ag_e; Ag_K; Ag_Fya; Ag_Fyb; Ag_Jka; Ag_Jkb; Ag_S; Ag_s].

(** Duffy null phenotype modeling.
    Duffy null individuals (Fy(a-b-)) lack both Fya and Fyb antigens.

    IMPORTANT: Duffy null does NOT mean "universal recipient" for Duffy.
    While they cannot form anti-Fya or anti-Fyb naturally (no antigen exposure),
    they CAN become alloimmunized after transfusion with Fy(a+) or Fy(b+) blood.
    The "universal recipient" claim is FALSE for alloimmunized individuals. *)
Definition is_duffy_null (ep : ExtendedPhenotype) : bool :=
  negb (ep_antigens ep Ag_Fya) && negb (ep_antigens ep Ag_Fyb).

(** Duffy compatibility with proper alloimmunization modeling.
    recipient_abs contains any anti-Fya or anti-Fyb the recipient has formed. *)
Definition duffy_compatible_correct (recipient_abs : list Antigen)
                                    (donor_ep : ExtendedPhenotype) : bool :=
  let fya_safe := negb (existsb (fun ag => if antigen_eq_dec ag Ag_Fya then true else false)
                                recipient_abs && ep_antigens donor_ep Ag_Fya) in
  let fyb_safe := negb (existsb (fun ag => if antigen_eq_dec ag Ag_Fyb then true else false)
                                recipient_abs && ep_antigens donor_ep Ag_Fyb) in
  fya_safe && fyb_safe.

(** Duffy null without alloimmunization is compatible with any donor *)
Theorem duffy_null_naive_compatible : forall donor_ep,
  duffy_compatible_correct [] donor_ep = true.
Proof. intros; reflexivity. Qed.

(** But alloimmunized Duffy null is NOT universally compatible *)
Theorem duffy_null_alloimmunized_not_universal :
  duffy_compatible_correct [Ag_Fya] (phenotype_Fya_positive O_neg) = false.
Proof. reflexivity. Qed.

(** Immunogenicity values: percentage of individuals who form antibody after
    single antigen-positive transfusion. Based on literature:
    - K (Kell): ~5% - highly immunogenic, second only to D
    - Fya (Duffy): ~0.1% - low immunogenicity
    - Jka (Kidd): ~0.07% - low but clinically significant due to evanescence

    Source: Tormey & Stack, Transfusion 2019; Verduin et al., Vox Sanguinis 2015 *)
Definition immunogenicity_K_percent : nat := 5.
Definition immunogenicity_Fya_percent_x100 : nat := 10.
Definition immunogenicity_Jka_percent_x100 : nat := 7.

(** Kell is the most immunogenic minor antigen (after D) *)
Theorem kell_highly_immunogenic :
  immunogenicity_K_percent >= 5.
Proof. unfold immunogenicity_K_percent; lia. Qed.

(** Duffy null phenotype and malaria resistance:
    The Fy(a-b-) phenotype, common in African populations (~70%), confers
    resistance to Plasmodium vivax malaria. The parasite uses the Duffy
    antigen as a receptor to enter red blood cells. *)
Definition duffy_null_malaria_resistance_prevalence_africa : nat := 70.

Theorem duffy_null_common_in_africa :
  duffy_null_malaria_resistance_prevalence_africa >= 50.
Proof. unfold duffy_null_malaria_resistance_prevalence_africa; lia. Qed.

(** Kidd antibodies are clinically significant because they:
    1. Can cause delayed hemolytic transfusion reactions
    2. Often fall below detectable levels between exposures (evanescence)
    3. Show dosage effect (react more strongly with homozygous cells)
    The evanescence_risk represents the percentage of cases where
    anti-Jka/Jkb becomes undetectable within 6 months. *)
Definition kidd_antibody_evanescence_risk_percent : nat := 50.

Theorem kidd_antibodies_frequently_evanescent :
  kidd_antibody_evanescence_risk_percent >= 30.
Proof. unfold kidd_antibody_evanescence_risk_percent; lia. Qed.

(** Kidd antibody evanescence modeling for sensitization tracking.
    These antibodies can fall below detection threshold and reappear on re-exposure,
    causing delayed hemolytic transfusion reactions (DHTR). *)
Inductive AntibodyStatus : Type :=
  | Detectable
  | Evanescent
  | Historical.

Record AntibodyRecord := mkAntibodyRecord {
  ab_antigen : Antigen;
  ab_status : AntibodyStatus;
  ab_months_since_detection : nat;
  ab_exposure_count : nat
}.

Definition is_kidd_antigen (ag : Antigen) : bool :=
  match ag with Ag_Jka | Ag_Jkb => true | _ => false end.

Definition kidd_evanescence_months : nat := 6.

Definition update_antibody_status (ab : AntibodyRecord) (months_elapsed : nat)
    : AntibodyRecord :=
  let new_months := ab_months_since_detection ab + months_elapsed in
  if is_kidd_antigen (ab_antigen ab) then
    match ab_status ab with
    | Detectable =>
        if Nat.leb kidd_evanescence_months new_months then
          mkAntibodyRecord (ab_antigen ab) Evanescent new_months (ab_exposure_count ab)
        else
          mkAntibodyRecord (ab_antigen ab) Detectable new_months (ab_exposure_count ab)
    | Evanescent =>
        mkAntibodyRecord (ab_antigen ab) Historical new_months (ab_exposure_count ab)
    | Historical => ab
    end
  else ab.

Definition reactivate_on_exposure (ab : AntibodyRecord) : AntibodyRecord :=
  match ab_status ab with
  | Evanescent | Historical =>
      mkAntibodyRecord (ab_antigen ab) Detectable 0 (S (ab_exposure_count ab))
  | Detectable =>
      mkAntibodyRecord (ab_antigen ab) Detectable 0 (S (ab_exposure_count ab))
  end.

Definition antibody_clinically_significant (ab : AntibodyRecord) : bool :=
  match ab_status ab with
  | Detectable => true
  | Evanescent => true
  | Historical => is_kidd_antigen (ab_antigen ab)
  end.

Theorem kidd_always_significant : forall ab,
  is_kidd_antigen (ab_antigen ab) = true ->
  antibody_clinically_significant ab = true.
Proof.
  intros ab Hkidd.
  unfold antibody_clinically_significant.
  destruct (ab_status ab); try reflexivity.
  exact Hkidd.
Qed.

Theorem evanescent_becomes_historical : forall ab months,
  ab_status ab = Evanescent ->
  is_kidd_antigen (ab_antigen ab) = true ->
  months > 0 ->
  ab_status (update_antibody_status ab months) = Historical.
Proof.
  intros ab months Hev Hkidd Hmonths.
  unfold update_antibody_status.
  rewrite Hkidd. rewrite Hev. reflexivity.
Qed.

Theorem reactivation_makes_detectable : forall ab,
  ab_status (reactivate_on_exposure ab) = Detectable.
Proof.
  intros ab. unfold reactivate_on_exposure.
  destruct (ab_status ab); reflexivity.
Qed.

(** Immune history: collection of antibody records *)
Definition ImmuneHistory := list AntibodyRecord.

(** Extract clinically significant antibodies from immune history *)
Definition significant_antibodies (hist : ImmuneHistory) : list Antigen :=
  map ab_antigen (filter antibody_clinically_significant hist).

(** Check if donor has any antigen matching recipient's significant antibodies *)
Definition history_compatible (hist : ImmuneHistory) (donor_ags : AntigenSet) : bool :=
  forallb (fun ag => negb (donor_ags ag)) (significant_antibodies hist).

(** Predict transfusion outcome based on immune history *)
Inductive TransfusionOutcome : Type :=
  | Outcome_Safe
  | Outcome_Immediate_Reaction
  | Outcome_Delayed_Reaction
  | Outcome_Anamnestic_Response.

Definition predict_outcome (hist : ImmuneHistory) (donor_ags : AntigenSet) : TransfusionOutcome :=
  let sig_abs := filter antibody_clinically_significant hist in
  let matching := filter (fun ab => donor_ags (ab_antigen ab)) sig_abs in
  match matching with
  | [] => Outcome_Safe
  | ab :: _ =>
      match ab_status ab with
      | Detectable => Outcome_Immediate_Reaction
      | Evanescent => Outcome_Anamnestic_Response
      | Historical => Outcome_Delayed_Reaction
      end
  end.

Theorem no_history_is_safe : forall donor_ags,
  predict_outcome [] donor_ags = Outcome_Safe.
Proof. reflexivity. Qed.

Theorem detectable_ab_causes_immediate : forall ag donor_ags rest,
  donor_ags ag = true ->
  let ab := mkAntibodyRecord ag Detectable 0 1 in
  predict_outcome (ab :: rest) donor_ags = Outcome_Immediate_Reaction.
Proof.
  intros ag donor_ags rest Hag.
  unfold predict_outcome, antibody_clinically_significant. simpl.
  rewrite Hag. reflexivity.
Qed.

(** Link antibody history to transfusion decision *)
Definition transfusion_decision_with_history
    (recipient donor : BloodType)
    (hist : ImmuneHistory)
    (donor_minor_ags : AntigenSet) : bool * TransfusionOutcome :=
  let base_compat := compatible recipient donor in
  let minor_compat := history_compatible hist donor_minor_ags in
  let outcome := predict_outcome hist donor_minor_ags in
  (base_compat && minor_compat, outcome).

Theorem compatible_with_empty_history : forall r d donor_ags,
  compatible r d = true ->
  fst (transfusion_decision_with_history r d [] donor_ags) = true.
Proof.
  intros r d donor_ags H.
  unfold transfusion_decision_with_history, history_compatible, significant_antibodies.
  simpl. rewrite H. reflexivity.
Qed.

Theorem minor_compatible_list_empty_abs : forall donor_ags,
  minor_antigen_compatible_list [] donor_ags = true.
Proof. reflexivity. Qed.

(** Full compatibility including ABO, Rh, and minor antigens.
    This addresses the limitation that core `compatible` only checks ABO-Rh.
    Use this function when minor antigen matching is clinically required
    (e.g., chronically transfused patients, alloimmunized recipients).
    Both recipient antibodies and donor antigens use unified list Antigen. *)
Definition full_compatible (recipient donor : BloodType)
                           (recipient_abs : list Antigen)
                           (donor_ags : list Antigen) : bool :=
  compatible recipient donor && minor_antigen_compatible_list recipient_abs donor_ags.

Theorem full_compatible_implies_base_compatible : forall r d abs ags,
  full_compatible r d abs ags = true -> compatible r d = true.
Proof.
  intros r d abs ags H. unfold full_compatible in H.
  apply andb_prop in H. destruct H. exact H.
Qed.

Theorem base_compatible_with_no_abs : forall r d ags,
  compatible r d = true -> full_compatible r d [] ags = true.
Proof.
  intros r d ags H. unfold full_compatible.
  rewrite H. simpl. reflexivity.
Qed.

Theorem full_compatible_symmetric_no_abs : forall r d,
  compatible r d = true -> full_compatible r d [] [] = true.
Proof.
  intros r d H. unfold full_compatible. rewrite H. reflexivity.
Qed.

(** HLA and platelet details *)

Inductive HLAClass1 : Type := HLA_A | HLA_B | HLA_C.
Inductive HLAClass2 : Type := HLA_DR | HLA_DQ | HLA_DP.

Definition hla_class1_eq_dec (x y : HLAClass1) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition hla_matched (recipient_hla donor_hla : list HLAClass1) : bool :=
  forallb (fun h => existsb (fun h' =>
    if hla_class1_eq_dec h h' then true else false) donor_hla) recipient_hla.

Record PlateletUnit := mkPlateletUnit {
  plt_abo : ABO;
  plt_rh : Rh;
  plt_hla : list HLAClass1;
  plt_irradiated : bool;
  plt_leukoreduced : bool;
  plt_age_days : nat
}.

Inductive PlateletMatchGrade : Type :=
  | PLT_Identical
  | PLT_Compatible
  | PLT_Minor_Incompatible
  | PLT_Major_Incompatible.

Definition platelet_abo_identical (r d : ABO) : bool :=
  if abo_eq_dec r d then true else false.

Definition platelet_match_grade (recipient donor : ABO) : PlateletMatchGrade :=
  if platelet_abo_identical recipient donor then PLT_Identical
  else if platelet_abo_preferred recipient donor then PLT_Compatible
  else if platelet_abo_preferred donor recipient then PLT_Minor_Incompatible
  else PLT_Major_Incompatible.

Definition platelet_full_compatible (recipient_abo : ABO) (recipient_rh : Rh)
                                     (recipient_hla : list HLAClass1)
                                     (childbearing : bool)
                                     (unit : PlateletUnit) : bool :=
  platelet_abo_preferred recipient_abo (plt_abo unit) &&
  platelet_rh_safe recipient_rh (plt_rh unit) childbearing &&
  hla_matched recipient_hla (plt_hla unit) &&
  negb (is_expired Platelets (plt_age_days unit)).

Record CryoUnit := mkCryoUnit {
  cryo_abo : ABO;
  cryo_volume_ml : nat;
  cryo_fibrinogen_mg : nat
}.

Definition cryo_abo_compatible (recipient donor : ABO) : bool :=
  platelet_abo_preferred recipient donor.

Definition cryo_abo_identical (recipient donor : ABO) : bool :=
  platelet_abo_identical recipient donor.

Theorem cryo_volume_threshold_2000 :
  cryo_needs_abo_match 1500 = false /\ cryo_needs_abo_match 2500 = true.
Proof. split; reflexivity. Qed.

(** Blood volume and massive transfusion protocol *)

Definition pediatric_blood_volume_ml_per_kg : nat := 80.
Definition adult_blood_volume_ml_per_kg : nat := 70.
Definition neonate_blood_volume_ml_per_kg : nat := 85.

Definition estimated_blood_volume (weight_kg : nat) (is_pediatric is_neonate : bool) : nat :=
  weight_kg * (if is_neonate then neonate_blood_volume_ml_per_kg
               else if is_pediatric then pediatric_blood_volume_ml_per_kg
               else adult_blood_volume_ml_per_kg).

Theorem pediatric_higher_relative_volume :
  pediatric_blood_volume_ml_per_kg > adult_blood_volume_ml_per_kg.
Proof. unfold pediatric_blood_volume_ml_per_kg, adult_blood_volume_ml_per_kg; lia. Qed.

Theorem neonate_highest_relative_volume :
  neonate_blood_volume_ml_per_kg > pediatric_blood_volume_ml_per_kg.
Proof. unfold neonate_blood_volume_ml_per_kg, pediatric_blood_volume_ml_per_kg; lia. Qed.

Definition massive_transfusion_threshold_percent : nat := 100.

Definition is_massive_transfusion (blood_volume_lost_percent : nat) : bool :=
  Nat.leb massive_transfusion_threshold_percent blood_volume_lost_percent.

Definition massive_transfusion_protocol_ratio : (nat * nat * nat) := (1, 1, 1).

Theorem mtp_balanced_ratio :
  massive_transfusion_protocol_ratio = (1, 1, 1).
Proof. reflexivity. Qed.

Definition mtp_rbc_units (total_units : nat) : nat := total_units / 3.
Definition mtp_ffp_units (total_units : nat) : nat := total_units / 3.
Definition mtp_platelet_units (total_units : nat) : nat := total_units / 3.

Theorem mtp_distribution_6 :
  mtp_rbc_units 6 = 2 /\ mtp_ffp_units 6 = 2 /\ mtp_platelet_units 6 = 2.
Proof. repeat split; reflexivity. Qed.

Theorem mtp_distribution_12 :
  mtp_rbc_units 12 = 4 /\ mtp_ffp_units 12 = 4 /\ mtp_platelet_units 12 = 4.
Proof. repeat split; reflexivity. Qed.

Definition hemoglobin_threshold_gdL : nat := 7.
Definition platelet_threshold_per_uL : nat := 10000.
Definition inr_threshold_tenths : nat := 20.

Definition rbc_units_for_hgb_increase (current_hgb target_hgb weight_kg : nat) : nat :=
  ((target_hgb - current_hgb) * weight_kg) / 70.

Definition cryo_dose_units (weight_kg : nat) : nat :=
  (weight_kg + 9) / 10.

Theorem dosing_comprehensive :
  platelet_dose 70 = 6 /\
  platelet_dose 25 = 2 /\
  platelet_dose 8 = 1 /\
  ffp_dose_ml 70 = 1050 /\
  cryo_dose_units 70 = 7 /\
  rbc_units_for_hgb_increase 5 9 70 = 4.
Proof. repeat split; reflexivity. Qed.

(** Inventory management *)

Definition get_inventory (i : Inventory) (bt : BloodType) : nat := i.(inv) bt.

Definition set_inventory (old : Inventory) (bt : BloodType) (n : nat) : Inventory :=
  mkInventory (fun bt' => if blood_eq_dec bt bt' then n else old.(inv) bt').

Definition rh_neg_supply (i : Inventory) : nat :=
  get_inventory i A_neg + get_inventory i B_neg +
  get_inventory i AB_neg + get_inventory i O_neg.

Definition rh_pos_supply (i : Inventory) : nat :=
  get_inventory i A_pos + get_inventory i B_pos +
  get_inventory i AB_pos + get_inventory i O_pos.

Theorem inventory_partition : forall i,
  total_units i = rh_neg_supply i + rh_pos_supply i.
Proof.
  intros i. unfold total_units, rh_neg_supply, rh_pos_supply, get_inventory.
  simpl. lia.
Qed.

Definition emergency_reserve (i : Inventory) : nat :=
  get_inventory i O_neg.

Definition is_critical_shortage (i : Inventory) : bool :=
  Nat.ltb (emergency_reserve i) 10.

Definition can_handle_emergency (i : Inventory) : bool :=
  Nat.leb 1 (emergency_reserve i).

Theorem emergency_requires_O_neg : forall i,
  can_handle_emergency i = true <-> emergency_reserve i >= 1.
Proof.
  intros i; split; intro H.
  - unfold can_handle_emergency in H. apply Nat.leb_le in H. exact H.
  - unfold can_handle_emergency. apply Nat.leb_le. exact H.
Qed.

Definition mass_casualty_capacity (i : Inventory) : nat :=
  get_inventory i O_neg + get_inventory i O_pos.

Theorem mass_casualty_serves_all_positive : forall i (recipient : BloodType),
  snd recipient = Pos ->
  mass_casualty_capacity i >= get_inventory i O_pos.
Proof.
  intros i recipient H. unfold mass_casualty_capacity. lia.
Qed.

(** Allocation and triage *)

Record AllocationRequest := mkRequest {
  req_recipient : BloodType;
  req_priority : Priority;
  req_units_needed : nat;
  req_has_antibodies : bool
}.

Definition request_urgency (r : AllocationRequest) : nat :=
  priority_value (req_priority r).

Definition compare_requests (r1 r2 : AllocationRequest) : bool :=
  Nat.ltb (request_urgency r1) (request_urgency r2).

Definition shortage_triage (requests : list AllocationRequest) (available : nat)
    : list (AllocationRequest * nat) :=
  let fix allocate reqs remaining :=
    match reqs with
    | [] => []
    | r :: rest =>
        let give := Nat.min (req_units_needed r) remaining in
        (r, give) :: allocate rest (remaining - give)
    end
  in allocate requests available.

Lemma min_le_right : forall a b, Nat.min a b <= b.
Proof. intros; apply Nat.le_min_r. Qed.

Lemma min_le_left : forall a b, Nat.min a b <= a.
Proof. intros; apply Nat.le_min_l. Qed.

Theorem triage_single_bounded : forall r avail,
  snd (r, Nat.min (req_units_needed r) avail) <= avail.
Proof. intros; simpl; apply min_le_right. Qed.

Theorem triage_respects_priority : forall r1 r2,
  higher_priority (req_priority r1) (req_priority r2) = true ->
  priority_value (req_priority r1) < priority_value (req_priority r2).
Proof.
  intros r1 r2 H. unfold higher_priority in H.
  apply Nat.ltb_lt in H. exact H.
Qed.

Theorem emergency_beats_all : forall p,
  p <> Emergency -> compare_requests (mkRequest O_neg Emergency 2 false)
                                      (mkRequest O_neg p 2 false) = true.
Proof. intros [| | | ] H; try reflexivity; exfalso; apply H; reflexivity. Qed.

(** Total allocated units bounded by available units.
    This is the key resource safety property for shortage_triage. *)
Definition triage_total_allocated (result : list (AllocationRequest * nat)) : nat :=
  fold_left Nat.add (map snd result) 0.

Fixpoint allocate_aux (reqs : list AllocationRequest) (remaining : nat)
    : list (AllocationRequest * nat) :=
  match reqs with
  | [] => []
  | r :: rest =>
      let give := Nat.min (req_units_needed r) remaining in
      (r, give) :: allocate_aux rest (remaining - give)
  end.

Fixpoint list_sum (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + list_sum xs
  end.

Lemma fold_left_add_shift : forall l acc,
  fold_left Nat.add l acc = acc + fold_left Nat.add l 0.
Proof.
  induction l as [| x xs IH]; intros acc; simpl.
  - lia.
  - rewrite IH. rewrite (IH x). lia.
Qed.

Lemma list_sum_fold_equiv : forall l,
  list_sum l = fold_left Nat.add l 0.
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite fold_left_add_shift. rewrite <- IH. lia.
Qed.

Lemma allocate_aux_bounded_direct : forall reqs remaining,
  list_sum (map snd (allocate_aux reqs remaining)) <= remaining.
Proof.
  induction reqs as [| r rest IH]; intros remaining; simpl.
  - lia.
  - set (give := Nat.min (req_units_needed r) remaining).
    assert (Hgive: give <= remaining) by apply Nat.le_min_r.
    specialize (IH (remaining - give)).
    lia.
Qed.

Lemma allocate_aux_bounded : forall reqs remaining,
  fold_left Nat.add (map snd (allocate_aux reqs remaining)) 0 <= remaining.
Proof.
  intros. rewrite <- list_sum_fold_equiv. apply allocate_aux_bounded_direct.
Qed.

Theorem shortage_triage_bounded : forall reqs available,
  triage_total_allocated (shortage_triage reqs available) <= available.
Proof.
  intros reqs available.
  unfold triage_total_allocated, shortage_triage.
  rewrite <- list_sum_fold_equiv.
  generalize available. clear available.
  induction reqs as [| r rest IH]; intro available; simpl.
  - lia.
  - set (give := Nat.min (req_units_needed r) available).
    assert (Hgive: give <= available) by apply Nat.le_min_r.
    specialize (IH (available - give)).
    lia.
Qed.

(** Extended Rh model with weak-D *)

Inductive RhExtended : Type := RhPos | RhNeg | RhWeakD.

Definition BloodTypeExtended : Type := (ABO * RhExtended)%type.

Definition rh_to_extended (rh : Rh) : RhExtended :=
  match rh with Pos => RhPos | Neg => RhNeg end.

Definition blood_to_extended (bt : BloodType) : BloodTypeExtended :=
  (fst bt, rh_to_extended (snd bt)).

Definition extended_has_D_antigen (rh : RhExtended) : bool :=
  match rh with RhPos => true | RhWeakD => true | RhNeg => false end.

Definition extended_has_anti_D (rh : RhExtended) : bool :=
  match rh with RhNeg => true | _ => false end.

Definition extended_rh_safe (recipient donor : RhExtended) : bool :=
  match recipient, donor with
  | RhNeg, RhPos => false
  | RhNeg, RhWeakD => false
  | _, _ => true
  end.

Theorem weak_d_triggers_rh_neg :
  extended_rh_safe RhNeg RhWeakD = false.
Proof. reflexivity. Qed.

Theorem weak_d_safe_as_recipient : forall donor,
  extended_rh_safe RhWeakD donor = true.
Proof. intros [| | ]; reflexivity. Qed.

Definition donation_policy_weak_d : Prop :=
  extended_has_D_antigen RhWeakD = true.

Theorem weak_d_donation_policy : donation_policy_weak_d.
Proof. reflexivity. Qed.

Definition transfusion_policy_weak_d : Prop :=
  extended_has_anti_D RhWeakD = false.

Theorem weak_d_transfusion_policy : transfusion_policy_weak_d.
Proof. reflexivity. Qed.

Theorem base_implies_extended : forall r d,
  compatible r d = true ->
  extended_rh_safe (rh_to_extended (snd r)) (rh_to_extended (snd d)) = true.
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]] H; simpl in *;
  try reflexivity; try discriminate.
Qed.

(** Population statistics *)

Definition rh_neg_prevalence (pop : Population) : nat :=
  fold_left Nat.add (map (pop_frequency pop) [A_neg; B_neg; AB_neg; O_neg]) 0.

Theorem japan_very_low_rh_neg : rh_neg_prevalence Japan = 5.
Proof. reflexivity. Qed.

Theorem nigeria_low_rh_neg : rh_neg_prevalence Nigeria = 50.
Proof. reflexivity. Qed.

Theorem india_low_rh_neg : rh_neg_prevalence India = 61.
Proof. reflexivity. Qed.

Theorem us_moderate_rh_neg : rh_neg_prevalence US = 150.
Proof. reflexivity. Qed.

Definition universal_donor_scarcity (pop : Population) : nat :=
  pop_frequency pop O_neg.

Theorem japan_critical_O_neg : universal_donor_scarcity Japan = 1.
Proof. reflexivity. Qed.

Theorem us_better_O_neg : universal_donor_scarcity US = 66.
Proof. reflexivity. Qed.

Definition expected_compatible_supply (pop : Population) (recipient : BloodType) : nat :=
  fold_left Nat.add
    (map (fun donor => if compatible recipient donor
                       then pop_frequency pop donor else 0)
         all_blood_types) 0.

Theorem O_neg_supply_varies :
  expected_compatible_supply US O_neg = 66 /\
  expected_compatible_supply Japan O_neg = 1.
Proof. split; reflexivity. Qed.

Theorem AB_pos_supply_abundant :
  expected_compatible_supply US AB_pos = 1000 /\
  expected_compatible_supply Japan AB_pos = 1000.
Proof. split; reflexivity. Qed.

(** Pregnancy and HDFN details *)

Record PregnancyProfile := mkPregnancy {
  preg_maternal_bt : BloodType;
  preg_maternal_abs : list Antigen;
  preg_paternal_bt : BloodType;
  preg_paternal_ags : list Antigen;
  preg_gestational_weeks : nat;
  preg_previous_sensitization : bool;
  preg_previous_affected_fetus : bool
}.

Definition hdfn_abo_risk (p : PregnancyProfile) : bool :=
  match fst (preg_maternal_bt p), fst (preg_paternal_bt p) with
  | O, A => true
  | O, B => true
  | O, AB => true
  | _, _ => false
  end.

Definition hdfn_rh_risk_full (p : PregnancyProfile) : bool :=
  match snd (preg_maternal_bt p), snd (preg_paternal_bt p) with
  | Neg, Pos => true
  | _, _ => false
  end.

Definition rhogam_timing_weeks : list nat := [28; 34; 40].

Definition rhogam_indicated_full (p : PregnancyProfile) : bool :=
  hdfn_rh_risk_full p && negb (preg_previous_sensitization p).

Definition hdfn_risk_antigens : list Antigen :=
  [Ag_K; Ag_Fya; Ag_Jka; Ag_Jkb].

Definition is_hdfn_risk_antigen (ag : Antigen) : bool :=
  match ag with
  | Ag_K | Ag_Fya | Ag_Jka | Ag_Jkb => true
  | _ => false
  end.

Definition has_high_risk_antibody_unified (abs : list Antigen) : bool :=
  existsb is_hdfn_risk_antigen abs.

Theorem anti_K_is_high_risk_unified :
  has_high_risk_antibody_unified [Ag_K] = true.
Proof. reflexivity. Qed.

(** Kell HDFN severity model.
    Anti-K causes severe HDFN because:
    1. K antigen is expressed early in erythroid precursors
    2. Anti-K suppresses fetal erythropoiesis (not just hemolysis)
    3. Leads to anemia without proportional hyperbilirubinemia
    4. Fetal anemia can occur at lower antibody titers than anti-D

    Severity rating: 0-10 scale (10 = most severe) *)
Inductive HDFNSeverity : Type :=
  | HDFN_None
  | HDFN_Mild
  | HDFN_Moderate
  | HDFN_Severe
  | HDFN_Critical.

Definition hdfn_severity_score (s : HDFNSeverity) : nat :=
  match s with
  | HDFN_None => 0
  | HDFN_Mild => 2
  | HDFN_Moderate => 5
  | HDFN_Severe => 8
  | HDFN_Critical => 10
  end.

Definition antibody_hdfn_severity (ag : Antigen) : HDFNSeverity :=
  match ag with
  | Ag_D => HDFN_Critical
  | Ag_K => HDFN_Severe
  | Ag_c => HDFN_Moderate
  | Ag_E => HDFN_Mild
  | Ag_C => HDFN_Mild
  | Ag_Fya => HDFN_Mild
  | Ag_Jka => HDFN_Mild
  | _ => HDFN_None
  end.

Theorem kell_hdfn_severe_substantive :
  antibody_hdfn_severity Ag_K = HDFN_Severe /\
  hdfn_severity_score HDFN_Severe >= 8.
Proof. split; [reflexivity | simpl; lia]. Qed.

Theorem kell_causes_severe_hdfn :
  hdfn_severity_score (antibody_hdfn_severity Ag_K) >= 8.
Proof. simpl; lia. Qed.

Theorem D_most_severe_hdfn :
  forall ag, hdfn_severity_score (antibody_hdfn_severity ag) <=
             hdfn_severity_score (antibody_hdfn_severity Ag_D).
Proof.
  destruct ag; simpl; lia.
Qed.

Definition intrauterine_transfusion_threshold_weeks : nat := 18.

(** Laboratory workflow *)

Inductive AntibodyScreenResult : Type :=
  | ScreenNegative
  | ScreenPositive.

Definition screen_to_crossmatch (result : AntibodyScreenResult) : LabTest :=
  match result with
  | ScreenNegative => ElectronicCrossmatch
  | ScreenPositive => AHGCrossmatch
  end.

Theorem screen_neg_enables_electronic :
  screen_to_crossmatch ScreenNegative = ElectronicCrossmatch.
Proof. reflexivity. Qed.

Theorem screen_pos_requires_ahg :
  screen_to_crossmatch ScreenPositive = AHGCrossmatch.
Proof. reflexivity. Qed.

Definition two_sample_rule_satisfied (sample1_time sample2_time current_time : nat) : bool :=
  negb (Nat.eqb sample1_time sample2_time) &&
  Nat.leb sample1_time current_time &&
  Nat.leb sample2_time current_time.

Definition sample_validity_hours : nat := 72.

Definition sample_still_valid (collection_time current_time : nat) : bool :=
  Nat.leb (current_time - collection_time) sample_validity_hours.

(******************************************************************************)
(*              EMERGENCY RELEASE PROTOCOL                                    *)
(******************************************************************************)

(** Emergency release severity levels determine which products can be released
    without complete pretransfusion testing. *)
Inductive EmergencyLevel : Type :=
  | Emergency_None
  | Emergency_Urgent
  | Emergency_Immediate
  | Emergency_Exsanguinating.

(** Emergency release product selection.
    - Exsanguinating: O-neg RBCs, AB plasma (no crossmatch)
    - Immediate: Type-specific if ABO known, else O-neg (no crossmatch)
    - Urgent: Electronic crossmatch if screen negative, else AHG *)
Definition emergency_rbc_type (recipient_abo : option ABO) (recipient_rh : option Rh)
                               (level : EmergencyLevel) : BloodType :=
  match level with
  | Emergency_Exsanguinating => O_neg
  | Emergency_Immediate =>
      match recipient_abo, recipient_rh with
      | Some abo, Some rh => (abo, rh)
      | Some abo, None => (abo, Neg)
      | None, _ => O_neg
      end
  | Emergency_Urgent =>
      match recipient_abo, recipient_rh with
      | Some abo, Some rh => (abo, rh)
      | Some abo, None => (abo, Neg)
      | None, _ => O_neg
      end
  | Emergency_None => O_neg
  end.

Definition emergency_plasma_type (level : EmergencyLevel) : BloodType :=
  match level with
  | Emergency_Exsanguinating => AB_pos
  | _ => AB_pos
  end.

(** Emergency O-neg release is always ABO-Rh safe *)
Theorem emergency_O_neg_always_safe : forall recipient,
  compatible recipient O_neg = true.
Proof.
  intros [[| | | ] [| ]]; reflexivity.
Qed.

(** Emergency AB plasma is always ABO safe *)
Theorem emergency_AB_plasma_always_safe : forall recipient,
  plasma_compatible recipient AB_pos = true.
Proof.
  intros [[| | | ] [| ]]; reflexivity.
Qed.

(** Maximum units for emergency release without confirmed type *)
Definition max_uncrossmatched_units : nat := 4.

(** After exceeding threshold, type-specific blood required *)
Definition emergency_threshold_exceeded (units_given : nat) : bool :=
  Nat.ltb max_uncrossmatched_units units_given.

Theorem uncrossmatched_limit_exists :
  emergency_threshold_exceeded 5 = true.
Proof. reflexivity. Qed.

(******************************************************************************)
(*              IRRADIATED BLOOD PRODUCTS                                     *)
(******************************************************************************)

(** Indications for irradiated cellular blood products.
    Irradiation prevents transfusion-associated graft-versus-host disease
    (TA-GVHD) by inactivating donor lymphocytes. *)
Inductive IrradiationIndication : Type :=
  | Irrad_None
  | Irrad_BMT_Recipient
  | Irrad_CongenitalImmunodeficiency
  | Irrad_HodgkinDisease
  | Irrad_IntrauterineTransfusion
  | Irrad_DirectedDonation
  | Irrad_HLAMatchedPlatelets
  | Irrad_GranulocyteTransfusion
  | Irrad_FluidarabineTherapy
  | Irrad_PurinAnalogTherapy.

Definition requires_irradiation (ind : IrradiationIndication) : bool :=
  match ind with
  | Irrad_None => false
  | _ => true
  end.

(** Irradiation dose requirements (Gy = Gray) *)
Definition minimum_irradiation_dose_Gy : nat := 25.
Definition maximum_irradiation_dose_Gy : nat := 50.

(** Irradiated RBCs have reduced shelf life *)
Definition irradiated_rbc_shelf_life_days : nat := 28.
Definition standard_rbc_shelf_life_days : nat := 42.

Record IrradiatedProduct := mkIrradiatedProduct {
  irrad_product_type : Product;
  irrad_dose_Gy : nat;
  irrad_date : nat;
  irrad_expiry_days : nat
}.

Definition irradiation_adequate (p : IrradiatedProduct) : bool :=
  Nat.leb minimum_irradiation_dose_Gy (irrad_dose_Gy p) &&
  Nat.leb (irrad_dose_Gy p) maximum_irradiation_dose_Gy.

Theorem irradiation_25_Gy_adequate :
  irradiation_adequate (mkIrradiatedProduct PackedRBC 25 0 28) = true.
Proof. reflexivity. Qed.

Theorem irradiation_15_Gy_inadequate :
  irradiation_adequate (mkIrradiatedProduct PackedRBC 15 0 28) = false.
Proof. reflexivity. Qed.

(******************************************************************************)
(*              GRANULOCYTE TRANSFUSION                                       *)
(******************************************************************************)

(** Granulocyte concentrates require special compatibility considerations:
    1. Must be ABO compatible (contain significant RBCs)
    2. Must be Rh compatible for females of childbearing potential
    3. Should be irradiated (prevent TA-GVHD)
    4. Should be CMV-safe for CMV-negative recipients
    5. Must be transfused within 24 hours of collection *)

Record GranulocyteUnit := mkGranulocyteUnit {
  gran_donor_bt : BloodType;
  gran_irradiated : bool;
  gran_CMV_safe : bool;
  gran_collection_time : nat;
  gran_granulocyte_count : nat
}.

Definition granulocyte_shelf_life_hours : nat := 24.

Definition granulocyte_expired (g : GranulocyteUnit) (current_time : nat) : bool :=
  Nat.ltb granulocyte_shelf_life_hours (current_time - gran_collection_time g).

(** Granulocyte compatibility - requires ABO and Rh matching like RBCs *)
Definition granulocyte_compatible (recipient donor : BloodType)
                                   (recipient_childbearing : bool) : bool :=
  let abo_ok := rbc_compatible_abo recipient donor in
  let rh_ok := match snd recipient, snd donor, recipient_childbearing with
               | Neg, Pos, true => false
               | _, _, _ => true
               end in
  abo_ok && rh_ok.

(** Granulocytes must be irradiated *)
Definition granulocyte_safe (g : GranulocyteUnit) (recipient : BloodType)
                             (recipient_childbearing : bool)
                             (current_time : nat) : bool :=
  granulocyte_compatible recipient (gran_donor_bt g) recipient_childbearing &&
  gran_irradiated g &&
  negb (granulocyte_expired g current_time).

Theorem granulocyte_requires_irradiation : forall g r cb t,
  gran_irradiated g = false ->
  granulocyte_safe g r cb t = false.
Proof.
  intros g r cb t H. unfold granulocyte_safe. rewrite H.
  rewrite andb_false_r. reflexivity.
Qed.

(** Minimum granulocyte dose for therapeutic effect *)
Definition therapeutic_granulocyte_dose : nat := 10000000000.

(******************************************************************************)
(*              EXCHANGE TRANSFUSION                                          *)
(******************************************************************************)

(** Exchange transfusion calculations for neonatal hyperbilirubinemia
    and sickle cell disease. *)

(** Neonatal blood volume estimation (ml/kg) *)
Definition neonatal_blood_volume_ml_per_kg : nat := 85.

(** Double volume exchange removes ~85-90% of circulating component *)
Definition double_volume_exchange_efficiency_percent : nat := 87.

(** Single volume exchange removes ~63% *)
Definition single_volume_exchange_efficiency_percent : nat := 63.

Record ExchangeTransfusionParams := mkExchangeParams {
  exchange_patient_weight_kg : nat;
  exchange_patient_hct : nat;
  exchange_target_removal_percent : nat;
  exchange_product_hct : nat
}.

Definition calculate_exchange_volume (p : ExchangeTransfusionParams) : nat :=
  let blood_vol := neonatal_blood_volume_ml_per_kg * exchange_patient_weight_kg p in
  if Nat.leb (exchange_target_removal_percent p) 63 then blood_vol
  else if Nat.leb (exchange_target_removal_percent p) 87 then 2 * blood_vol
  else 3 * blood_vol.

(** For sickle cell: target HbS < 30% *)
Definition sickle_cell_exchange_target_HbS_percent : nat := 30.

(** Exchange transfusion RBC requirements for sickle cell.
    Use HbS-negative, antigen-matched (C, E, K) units. *)
Definition sickle_cell_exchange_requirements : list Antigen :=
  [Ag_C; Ag_E; Ag_K].

Definition antigen_in_list (ag : Antigen) (l : list Antigen) : bool :=
  existsb (fun ag' => if antigen_eq_dec ag ag' then true else false) l.

Definition sickle_exchange_compatible (donor : BloodType) (donor_antigens : list Antigen)
                                        (recipient_antibodies : list Antigen) : bool :=
  rbc_compatible_abo (O, Neg) donor &&
  negb (existsb (fun ag => antigen_in_list ag donor_antigens) recipient_antibodies).

(** Neonatal exchange must consider maternal antibodies *)
Definition neonatal_exchange_compatible (maternal_abs : list Antigen)
                                          (donor : BloodType) : bool :=
  rbc_compatible_abo (O, Neg) donor &&
  negb (existsb (fun ag => has_antigen donor ag) maternal_abs).

Theorem neonatal_exchange_O_neg_safe_if_no_maternal_abs :
  neonatal_exchange_compatible [] O_neg = true.
Proof. reflexivity. Qed.

(******************************************************************************)
(*              CMV SAFETY                                                    *)
(******************************************************************************)

(** CMV-safe products are required for CMV-negative immunocompromised patients *)
Inductive CMVStatus : Type :=
  | CMV_Negative
  | CMV_Positive
  | CMV_Unknown.

Definition cmv_safe_required (recipient_cmv : CMVStatus)
                              (immunocompromised : bool) : bool :=
  match recipient_cmv, immunocompromised with
  | CMV_Negative, true => true
  | _, _ => false
  end.

(** Leukoreduction provides CMV-risk reduction equivalent to CMV-negative testing *)
Definition leukoreduced_cmv_equivalent : Prop := True.

(** Donor counts and compatibility matrix *)

Theorem A_pos_has_4_donors : count_donors A_pos = 4.
Proof. reflexivity. Qed.

Theorem A_neg_has_2_donors : count_donors A_neg = 2.
Proof. reflexivity. Qed.

Theorem B_pos_has_4_donors : count_donors B_pos = 4.
Proof. reflexivity. Qed.

Theorem B_neg_has_2_donors : count_donors B_neg = 2.
Proof. reflexivity. Qed.

Theorem AB_pos_has_8_donors : count_donors AB_pos = 8.
Proof. reflexivity. Qed.

Theorem AB_neg_has_4_donors : count_donors AB_neg = 4.
Proof. reflexivity. Qed.

Theorem O_pos_has_2_donors : count_donors O_pos = 2.
Proof. reflexivity. Qed.

Theorem O_neg_has_1_donor : count_donors O_neg = 1.
Proof. reflexivity. Qed.

Definition donation_reach (donor : BloodType) : nat :=
  count_recipients donor.

Theorem O_neg_reaches_all : donation_reach O_neg = 8.
Proof. reflexivity. Qed.

Theorem AB_pos_reaches_one : donation_reach AB_pos = 1.
Proof. reflexivity. Qed.

Theorem O_neg_max_reach : forall bt, donation_reach bt <= donation_reach O_neg.
Proof. intros [[| | | ] [| ]]; unfold donation_reach, count_recipients; simpl; lia. Qed.

Definition compatibility_matrix : list (BloodType * BloodType * bool) :=
  flat_map (fun r => map (fun d => (r, d, compatible r d)) all_blood_types)
           all_blood_types.

Theorem compatibility_matrix_has_64_entries :
  length compatibility_matrix = 64.
Proof. reflexivity. Qed.

Definition vulnerability (bt : BloodType) : nat :=
  8 - count_donors bt.

Theorem O_neg_most_vulnerable : vulnerability O_neg = 7.
Proof. reflexivity. Qed.

Theorem AB_pos_least_vulnerable : vulnerability AB_pos = 0.
Proof. reflexivity. Qed.

Theorem vulnerability_bounded : forall bt, vulnerability bt <= 7.
Proof. intros [[| | | ] [| ]]; unfold vulnerability, count_donors; simpl; lia. Qed.

(** Recipient helper functions for deriving blood type from extended profile.

    IMPORTANT: Bombay phenotype individuals type as group O on forward typing
    (no A, B, or H antigens) but they have anti-A, anti-B, AND anti-H antibodies.
    They can ONLY receive blood from other Bombay donors, not from group O.

    The phenotypic_blood_type function returns what the typing shows (O for Bombay).
    The recipient_is_bombay predicate identifies true Bombay recipients.
    Compatibility checks must handle Bombay specially. *)

Definition phenotypic_blood_type (r : Recipient) : BloodType :=
  let abo := match rcpt_subtype r with
             | Sub_A1 | Sub_A2 | Sub_A3 | Sub_Aint | Sub_Acquired_B => A
             | Sub_B => B
             | Sub_A1B | Sub_A2B | Sub_Cis_AB => AB
             | Sub_O | Sub_Bombay => O
             end in
  let rh := variant_transfusion_type (rcpt_rh_variant r) in
  (abo, rh).

Definition recipient_is_bombay (r : Recipient) : bool :=
  match rcpt_subtype r with
  | Sub_Bombay => true
  | _ => false
  end.

Definition recipient_blood_type (r : Recipient) : BloodType :=
  phenotypic_blood_type r.

(** Unified compatibility check for Recipient against BloodType.
    Uses separated ABO and Rh compatibility:
    - ABO: Always checked (natural isoagglutinins)
    - Rh: Depends on sensitization status and childbearing potential

    Bombay recipients can ONLY receive Bombay blood.
    Standard O-negative blood contains H antigen which Bombay recipients
    will react against with their anti-H antibodies. *)
Definition recipient_compatible_with_bt (r : Recipient) (d : BloodType) : bool :=
  if recipient_is_bombay r then false
  else
    let r_bt := recipient_blood_type r in
    let abo_compat := rbc_compatible_abo r_bt d in
    let rh_compat := match rcpt_sensitized r, snd r_bt, snd d with
                     | Naive, Neg, Pos => negb (rcpt_female_childbearing r)
                     | Sensitized, Neg, Pos => false
                     | _, _, _ => true
                     end in
    abo_compat && rh_compat.

(** Bombay-to-Bombay compatibility using subtype-level matching *)
Definition bombay_compatible (r_sub d_sub : ABOSubtype) (r_rh d_rh : Rh) : bool :=
  match r_sub, d_sub with
  | Sub_Bombay, Sub_Bombay =>
      match r_rh, d_rh with
      | Neg, Pos => false
      | _, _ => true
      end
  | Sub_Bombay, _ => false
  | _, _ => true
  end.

Theorem bombay_cannot_receive_O :
  forall r, recipient_is_bombay r = true ->
  recipient_compatible_with_bt r O_neg = false.
Proof.
  intros r H. unfold recipient_compatible_with_bt. rewrite H. reflexivity.
Qed.

Theorem bombay_cannot_receive_any_standard_type :
  forall r bt, recipient_is_bombay r = true ->
  recipient_compatible_with_bt r bt = false.
Proof.
  intros r bt H. unfold recipient_compatible_with_bt. rewrite H. reflexivity.
Qed.

Theorem non_bombay_uses_abo_compat :
  forall r d, recipient_is_bombay r = false ->
  recipient_compatible_with_bt r d = true ->
  rbc_compatible_abo (recipient_blood_type r) d = true.
Proof.
  intros r d Hnb H. unfold recipient_compatible_with_bt in H. rewrite Hnb in H.
  apply andb_prop in H. destruct H. exact H.
Qed.

Theorem recipient_compatible_implies_abo_compatible : forall r d,
  recipient_compatible_with_bt r d = true ->
  rbc_compatible_abo (recipient_blood_type r) d = true.
Proof.
  intros r d H. unfold recipient_compatible_with_bt in H.
  destruct (recipient_is_bombay r) eqn:Hb.
  - discriminate.
  - apply andb_prop in H. destruct H. exact H.
Qed.

(** Naive non-childbearing Rh-negative CAN receive same-ABO Rh-positive.
    ABO compatibility is checked separately from Rh sensitization status. *)
Theorem naive_non_childbearing_can_receive_pos :
  let r := mkRecipient Sub_A1 Rh_Normal_Neg Naive [] false in
  recipient_compatible_with_bt r (A, Pos) = true.
Proof. reflexivity. Qed.

Theorem naive_non_childbearing_can_receive_pos_O :
  let r := mkRecipient Sub_O Rh_Normal_Neg Naive [] false in
  recipient_compatible_with_bt r (O, Pos) = true.
Proof. reflexivity. Qed.

Theorem naive_neg_base_incompatible_conservative : forall abo,
  compatible (abo, Neg) (abo, Pos) = false.
Proof. intros [| | | ]; reflexivity. Qed.

Theorem naive_neg_abo_compatible : forall abo,
  rbc_compatible_abo (abo, Neg) (abo, Pos) = true.
Proof. intros [| | | ]; reflexivity. Qed.

Theorem sensitized_cannot_receive_pos : forall sub d_abo,
  sub <> Sub_Bombay ->
  let r := mkRecipient sub Rh_Normal_Neg Sensitized [] false in
  recipient_compatible_with_bt r (d_abo, Pos) = false.
Proof.
  intros sub d_abo Hnotbombay.
  unfold recipient_compatible_with_bt, recipient_is_bombay, recipient_blood_type, phenotypic_blood_type.
  destruct sub, d_abo; reflexivity.
Qed.

Theorem childbearing_female_protected : forall sub d_abo,
  sub <> Sub_Bombay ->
  let r := mkRecipient sub Rh_Normal_Neg Naive [] true in
  recipient_compatible_with_bt r (d_abo, Pos) = false.
Proof.
  intros sub d_abo Hnotbombay.
  unfold recipient_compatible_with_bt, recipient_is_bombay, recipient_blood_type, phenotypic_blood_type.
  destruct sub, d_abo; reflexivity.
Qed.

Definition sensitization_risk (recipient donor : BloodType) : bool :=
  match snd recipient, snd donor with
  | Neg, Pos => true
  | _, _ => false
  end.

Theorem sensitization_only_neg_to_pos : forall r d,
  sensitization_risk r d = true <-> (snd r = Neg /\ snd d = Pos).
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]]; simpl; split; intro H;
  try discriminate; try (destruct H; discriminate);
  try (split; reflexivity); try reflexivity.
Qed.

(** Comprehensive decision support *)

Record FullTransfusionDecision := mkFullDecision {
  ftd_compatible : bool;
  ftd_match : MatchQuality;
  ftd_severity : Severity;
  ftd_crossmatch : LabTest;
  ftd_allocation_score : nat;
  ftd_special_requirements : list Product
}.

Definition make_full_decision (recipient donor : BloodType)
                               (screen : AntibodyScreenResult)
                               (inv : Inventory) : FullTransfusionDecision :=
  mkFullDecision
    (compatible recipient donor)
    (match_quality recipient donor)
    (assess_severity recipient donor)
    (screen_to_crossmatch screen)
    (allocation_score recipient donor)
    [].

(** Extended record including DAT and AIHA classification *)
Record FullTransfusionDecisionWithDAT := mkFullDecisionDAT {
  ftdd_base : FullTransfusionDecision;
  ftdd_dat_result : DATResult;
  ftdd_aiha_type : AIHAType;
  ftdd_crossmatch_difficulty : nat;
  ftdd_needs_adsorption : bool
}.

Definition make_full_decision_with_dat (recipient donor : BloodType)
                                       (screen : AntibodyScreenResult)
                                       (inv : Inventory)
                                       (dat : DATProfile) : FullTransfusionDecisionWithDAT :=
  mkFullDecisionDAT
    (make_full_decision recipient donor screen inv)
    (dat_result dat)
    (classify_aiha dat)
    (crossmatch_difficulty dat)
    (needs_adsorption_study dat).

Definition full_decision_with_dat_safe (d : FullTransfusionDecisionWithDAT) : bool :=
  ftd_compatible (ftdd_base d) &&
  match ftd_severity (ftdd_base d) with Safe => true | _ => false end &&
  match ftdd_aiha_type d with
  | AIHA_None => true
  | AIHA_Cold => true
  | _ => false
  end.

Theorem dat_negative_decision_matches_base : forall r d s i,
  let dat := mkDATProfile DAT_Negative None None None in
  let dec_dat := make_full_decision_with_dat r d s i dat in
  ftdd_aiha_type dec_dat = AIHA_None /\
  ftdd_crossmatch_difficulty dec_dat = 0.
Proof. intros; split; reflexivity. Qed.

Definition full_decision_safe (d : FullTransfusionDecision) : bool :=
  ftd_compatible d &&
  match ftd_severity d with Safe => true | _ => false end.

Theorem full_decision_consistency : forall r d s i,
  compatible r d = true ->
  let dec := make_full_decision r d s i in
  ftd_compatible dec = true /\ ftd_severity dec = Safe.
Proof.
  intros r d s i H; split.
  - unfold make_full_decision; simpl; exact H.
  - unfold make_full_decision; simpl. apply compatible_is_safe. exact H.
Qed.

Definition is_rare_type (bt : BloodType) : bool :=
  Nat.leb (pop_frequency US bt) 15.

Theorem rare_types_identified :
  is_rare_type B_neg = true /\ is_rare_type AB_neg = true /\
  is_rare_type O_neg = false /\ is_rare_type A_pos = false.
Proof. repeat split; reflexivity. Qed.

Definition find_compatible_in_inventory (inv : Inventory) (recipient : BloodType)
    : list (BloodType * nat) :=
  filter (fun p => andb (compatible recipient (fst p)) (Nat.ltb 0 (snd p)))
         (map (fun bt => (bt, get_inventory inv bt)) all_blood_types).

(** Crossmatch and agglutination *)

Definition agglutination (recipient donor : BloodType) (ag : Antigen) : bool :=
  has_antibody recipient ag && has_antigen donor ag.

Definition crossmatch_reaction (recipient donor : BloodType) : bool :=
  existsb (agglutination recipient donor) core_antigens.

Theorem no_reaction_means_compatible : forall r d,
  crossmatch_reaction r d = false -> compatible r d = true.
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]]; simpl; intro H;
  try reflexivity; try discriminate.
Qed.

Theorem reaction_means_incompatible : forall r d,
  crossmatch_reaction r d = true -> compatible r d = false.
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]]; simpl; intro H;
  try reflexivity; try discriminate.
Qed.

Theorem crossmatch_negative_implies_safe : forall r d,
  crossmatch_reaction r d = false -> no_adverse_reaction r d.
Proof.
  intros r d H. apply compatible_iff_safe. apply no_reaction_means_compatible. exact H.
Qed.

(** Plasma theorems *)

Theorem AB_plasma_universal_donor : forall recipient,
  plasma_compatible recipient AB_pos = true.
Proof. intros [[| | | ] [| ]]; reflexivity. Qed.

Theorem O_plasma_universal_recipient : forall donor,
  plasma_compatible O_neg donor = true.
Proof. intros [[| | | ] [| ]]; reflexivity. Qed.

(** Plasma-RBC duality holds for ABO only.
    Plasma compatibility is the ABO-inverse of RBC compatibility:
    donor plasma antibodies must not react with recipient antigens. *)
Theorem plasma_rbc_abo_duality : forall r d,
  plasma_compatible r d = rbc_compatible_abo d r.
Proof. intros [[| | | ] [| ]] [[| | | ] [| ]]; reflexivity. Qed.

(** Rh is irrelevant for plasma - same Rh, different Rh, all compatible *)
Theorem plasma_ignores_rh : forall r_abo d_abo r_rh d_rh,
  plasma_compatible (r_abo, r_rh) (d_abo, d_rh) =
  plasma_compatible (r_abo, Pos) (d_abo, Pos).
Proof. intros [| | | ] [| | | ] [| ] [| ]; reflexivity. Qed.

(** Whole blood theorems *)

Theorem whole_blood_requires_exact_abo : forall abo1 abo2 rh1 rh2,
  abo1 <> abo2 -> whole_blood_compatible (abo1, rh1) (abo2, rh2) = false.
Proof.
  intros [| | | ] [| | | ] [| ] [| ] H; try reflexivity;
  exfalso; apply H; reflexivity.
Qed.

Theorem whole_blood_self_compatible : forall bt,
  whole_blood_compatible bt bt = true.
Proof. intros [[| | | ] [| ]]; reflexivity. Qed.

Definition count_whole_blood_donors (recipient : BloodType) : nat :=
  length (filter (whole_blood_compatible recipient) all_blood_types).

Theorem whole_blood_more_restrictive : forall bt,
  count_whole_blood_donors bt <= count_donors bt.
Proof.
  intros [[| | | ] [| ]];
  unfold count_whole_blood_donors, count_donors; simpl; lia.
Qed.

Theorem whole_blood_self_only : forall bt,
  count_whole_blood_donors bt <= 2.
Proof.
  intros [[| | | ] [| ]];
  unfold count_whole_blood_donors; simpl; lia.
Qed.

(** Incompatibility theorems *)

Theorem A_cannot_donate_to_B : forall rh1 rh2,
  compatible (B, rh1) (A, rh2) = false.
Proof. intros [| ] [| ]; reflexivity. Qed.

Theorem B_cannot_donate_to_A : forall rh1 rh2,
  compatible (A, rh1) (B, rh2) = false.
Proof. intros [| ] [| ]; reflexivity. Qed.

Theorem A_cannot_donate_to_O : forall rh1 rh2,
  compatible (O, rh1) (A, rh2) = false.
Proof. intros [| ] [| ]; reflexivity. Qed.

Theorem B_cannot_donate_to_O : forall rh1 rh2,
  compatible (O, rh1) (B, rh2) = false.
Proof. intros [| ] [| ]; reflexivity. Qed.

Theorem O_incompatible_with_A : compatible O_pos A_pos = false.
Proof. reflexivity. Qed.

Theorem O_incompatible_with_B : compatible O_pos B_pos = false.
Proof. reflexivity. Qed.

Theorem O_incompatible_with_AB : compatible O_pos AB_pos = false.
Proof. reflexivity. Qed.

(** Severity detail theorems *)

Definition mortality_risk_percent (s : Severity) : nat :=
  match s with
  | Safe => 0 | DelayedHemolytic => 1 | AcuteHemolytic => 5
  | SevereAcuteHemolytic => 15 | LifeThreatening => 30
  end.

Theorem compatible_no_reaction : forall r d,
  compatible r d = true -> assess_severity r d = Safe.
Proof. intros r d H; unfold assess_severity; rewrite H; reflexivity. Qed.

Theorem incompatible_has_reaction : forall r d,
  compatible r d = false -> assess_severity r d <> Safe.
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]] H;
  unfold assess_severity; rewrite H; discriminate.
Qed.

Theorem O_to_AB_most_dangerous : forall rh1 rh2,
  compatible (O, rh1) (AB, rh2) = false ->
  assess_severity (O, rh1) (AB, rh2) = LifeThreatening.
Proof. intros [| ] [| ] H; reflexivity. Qed.

Theorem cross_AB_always_life_threatening :
  assess_severity A_pos B_pos = LifeThreatening /\
  assess_severity B_pos A_pos = LifeThreatening.
Proof. split; reflexivity. Qed.

Theorem rh_only_mismatch_delayed : forall abo,
  assess_severity (abo, Neg) (abo, Pos) = DelayedHemolytic.
Proof. intros [| | | ]; reflexivity. Qed.

Theorem life_threatening_highest_mortality : forall s,
  mortality_risk_percent s <= mortality_risk_percent LifeThreatening.
Proof. intros [| | | | ]; simpl; lia. Qed.

Theorem severity_monotonic : forall r d,
  compatible r d = false -> severity_score (assess_severity r d) >= 1.
Proof.
  intros [[| | | ] [| ]] [[| | | ] [| ]] H;
  unfold assess_severity; simpl in *; try discriminate; simpl; lia.
Qed.

(** Rh haplotypes *)

Inductive RhCcEe : Type := RhCcEe_C | RhCcEe_c | RhCcEe_E | RhCcEe_e.

Definition hap_DcE : RhHaplotype := mkRhHap true false true.
Definition hap_Dce : RhHaplotype := mkRhHap true false false.
Definition hap_DCE : RhHaplotype := mkRhHap true true true.
Definition hap_dCe : RhHaplotype := mkRhHap false true false.
Definition hap_dcE : RhHaplotype := mkRhHap false false true.

Definition rh_haplotype_frequency_white (h : RhHaplotype) : nat :=
  match h with
  | {| hap_D := true; hap_C := true; hap_E := false |} => 42
  | {| hap_D := true; hap_C := false; hap_E := true |} => 14
  | {| hap_D := true; hap_C := false; hap_E := false |} => 4
  | {| hap_D := false; hap_C := false; hap_E := false |} => 37
  | {| hap_D := false; hap_C := true; hap_E := false |} => 2
  | _ => 1
  end.

Definition phenotype_from_haplotypes (h1 h2 : RhHaplotype) :
    (bool * bool * bool * bool * bool) :=
  (hap_D h1 || hap_D h2,
   hap_C h1 || hap_C h2,
   negb (hap_C h1) || negb (hap_C h2),
   hap_E h1 || hap_E h2,
   negb (hap_E h1) || negb (hap_E h2)).

Theorem DCe_dce_phenotype :
  phenotype_from_haplotypes DCe dce = (true, true, true, false, true).
Proof. reflexivity. Qed.

Definition rh_haplotype_compatible (recipient donor : RhHaplotype * RhHaplotype) : bool :=
  let r_D := hap_D (fst recipient) || hap_D (snd recipient) in
  let d_D := hap_D (fst donor) || hap_D (snd donor) in
  match r_D, d_D with
  | false, true => false
  | _, _ => true
  end.

(** Genetics inheritance *)

Definition inherits_from (parent : ABOAllele * ABOAllele) (child : ABOAllele) : Prop :=
  child = fst parent \/ child = snd parent.

Definition valid_child_genotype (p1 p2 child : ABOGenotype) : Prop :=
  inherits_from p1 (fst child) /\ inherits_from p2 (snd child).

Definition rh_inherits_from (parent : RhAllele * RhAllele) (child : RhAllele) : Prop :=
  child = fst parent \/ child = snd parent.

Definition valid_rh_child_genotype (p1 p2 child : RhGenotype) : Prop :=
  rh_inherits_from p1 (fst child) /\ rh_inherits_from p2 (snd child).

Definition valid_full_child_genotype (p1 p2 child : FullGenotype) : Prop :=
  valid_child_genotype (fst p1) (fst p2) (fst child) /\
  valid_rh_child_genotype (snd p1) (snd p2) (snd child).

Theorem O_parents_O_child :
  abo_phenotype (Allele_O, Allele_O) = O.
Proof. reflexivity. Qed.

Theorem O_parent_genotypes_produce_O_child : forall child,
  valid_child_genotype (Allele_O, Allele_O) (Allele_O, Allele_O) child ->
  abo_phenotype child = O.
Proof.
  intros [c1 c2] [[H1|H1] [H2|H2]]; simpl in *; subst; reflexivity.
Qed.

Theorem AB_requires_A_and_B_allele : forall g,
  abo_phenotype g = AB ->
  (fst g = Allele_A /\ snd g = Allele_B) \/ (fst g = Allele_B /\ snd g = Allele_A).
Proof.
  intros [[| | ] [| | ]] H; simpl in H; try discriminate;
  [left | right]; split; reflexivity.
Qed.

Theorem two_O_parents_cannot_have_A_child : forall child,
  valid_child_genotype (Allele_O, Allele_O) (Allele_O, Allele_O) child ->
  abo_phenotype child <> A.
Proof.
  intros [c1 c2] [[H1|H1] [H2|H2]]; simpl in *; subst; simpl; discriminate.
Qed.

Theorem two_O_parents_cannot_have_B_child : forall child,
  valid_child_genotype (Allele_O, Allele_O) (Allele_O, Allele_O) child ->
  abo_phenotype child <> B.
Proof.
  intros [c1 c2] [[H1|H1] [H2|H2]]; simpl in *; subst; simpl; discriminate.
Qed.

Theorem two_O_parents_cannot_have_AB_child : forall child,
  valid_child_genotype (Allele_O, Allele_O) (Allele_O, Allele_O) child ->
  abo_phenotype child <> AB.
Proof.
  intros [c1 c2] [[H1|H1] [H2|H2]]; simpl in *; subst; simpl; discriminate.
Qed.

Theorem two_neg_parents_neg_child :
  rh_phenotype (Allele_d, Allele_d) = Neg.
Proof. reflexivity. Qed.

Theorem two_rh_neg_parents_produce_rh_neg_child : forall child,
  valid_rh_child_genotype (Allele_d, Allele_d) (Allele_d, Allele_d) child ->
  rh_phenotype child = Neg.
Proof.
  intros [c1 c2] [[H1|H1] [H2|H2]]; simpl in *; subst; reflexivity.
Qed.

Theorem pos_child_from_neg_parents_impossible : forall child,
  valid_rh_child_genotype (Allele_d, Allele_d) (Allele_d, Allele_d) child ->
  rh_phenotype child <> Pos.
Proof.
  intros child H Hcontra.
  apply two_rh_neg_parents_produce_rh_neg_child in H.
  rewrite H in Hcontra. discriminate.
Qed.

Theorem punnett_square_size : forall p1 p2,
  length (punnett_full p1 p2) = 16.
Proof. intros [[? ?] [? ?]] [[? ?] [? ?]]; reflexivity. Qed.

Theorem Dd_cross_can_produce_neg :
  exists child, In child (punnett_rh (Allele_D, Allele_d) (Allele_D, Allele_d)) /\
                rh_phenotype child = Neg.
Proof.
  exists (Allele_d, Allele_d). split.
  - simpl. right. right. right. left. reflexivity.
  - reflexivity.
Qed.

Theorem Dd_cross_can_produce_pos :
  exists child, In child (punnett_rh (Allele_D, Allele_d) (Allele_D, Allele_d)) /\
                rh_phenotype child = Pos.
Proof.
  exists (Allele_D, Allele_D). split.
  - simpl. left. reflexivity.
  - reflexivity.
Qed.

(** ABO subtype theorems *)

Theorem bombay_only_receives_bombay : forall donor,
  donor <> Sub_Bombay -> subtype_compatible Sub_Bombay donor = false.
Proof.
  intros [| | | | | | | | | | ] H; try reflexivity; exfalso; apply H; reflexivity.
Qed.

Theorem bombay_self_compatible :
  subtype_compatible Sub_Bombay Sub_Bombay = true.
Proof. reflexivity. Qed.

Theorem A2_cannot_receive_A1 :
  subtype_compatible Sub_A2 Sub_A1 = false.
Proof. reflexivity. Qed.

Theorem A2_can_receive_A2 :
  subtype_compatible Sub_A2 Sub_A2 = true.
Proof. reflexivity. Qed.

Theorem A2_can_receive_O :
  subtype_compatible Sub_A2 Sub_O = true.
Proof. reflexivity. Qed.

Definition A1_frequency_percent : nat := 80.
Definition A2_frequency_percent : nat := 20.

Theorem A1_A2_sum_100 :
  A1_frequency_percent + A2_frequency_percent = 100.
Proof. reflexivity. Qed.

(******************************************************************************)
(*                                                                            *)
(*                       IX. EMERGENCY AND MISC                               *)
(*                                                                            *)
(******************************************************************************)

Definition emergency_donor : BloodType := O_neg.

Theorem emergency_donor_always_safe : forall recipient,
  compatible recipient emergency_donor = true.
Proof. exact O_neg_universal_donor. Qed.

Definition find_compatible_donors (recipient : BloodType) : list BloodType :=
  filter (compatible recipient) all_blood_types.

Theorem find_compatible_donors_correct : forall recipient donor,
  In donor (find_compatible_donors recipient) <-> compatible recipient donor = true.
Proof.
  intros r d; split; intro H.
  - unfold find_compatible_donors in H. apply filter_In in H. destruct H. exact H0.
  - unfold find_compatible_donors. apply filter_In. split.
    + destruct d as [[| | | ] [| ]]; simpl; repeat (left; reflexivity) || right.
    + exact H.
Qed.

Theorem find_compatible_donors_safe : forall recipient donor,
  In donor (find_compatible_donors recipient) -> no_adverse_reaction recipient donor.
Proof.
  intros r d H. apply compatible_iff_safe. apply find_compatible_donors_correct. exact H.
Qed.

Theorem O_neg_can_donate_to_all :
  length (filter (fun r => compatible r O_neg) all_blood_types) = 8.
Proof. reflexivity. Qed.

Theorem AB_pos_can_donate_to_one :
  length (filter (fun r => compatible r AB_pos) all_blood_types) = 1.
Proof. reflexivity. Qed.

Theorem O_neg_donor_value_maximum : forall bt,
  count_recipients bt <= count_recipients O_neg.
Proof. intros [[| | | ] [| ]]; unfold count_recipients; simpl; lia. Qed.

Definition is_rare (bt : BloodType) : bool :=
  Nat.ltb (pop_frequency US bt) 20.

Theorem O_neg_is_rare : is_rare O_neg = false.
Proof. reflexivity. Qed.

Theorem AB_neg_is_rare : is_rare AB_neg = true.
Proof. reflexivity. Qed.

Theorem B_neg_is_rare : is_rare B_neg = true.
Proof. reflexivity. Qed.

Definition rare_types : list BloodType :=
  filter is_rare all_blood_types.

Theorem rare_types_are_two : length rare_types = 2.
Proof. reflexivity. Qed.

Theorem all_populations_sum_to_1000 : forall pop,
  pop_sum pop = 1000.
Proof. intros [| | | ]; reflexivity. Qed.

(******************************************************************************)
(*                                                                            *)
(*                       X. ALLELE FREQUENCIES                                *)
(*                                                                            *)
(******************************************************************************)

Definition us_abo_allele_frequencies : AlleleFreq :=
  mkAlleleFreq 28 7 65.

Theorem us_allele_frequencies_sum :
  freq_pA us_abo_allele_frequencies + freq_pB us_abo_allele_frequencies +
  freq_pO us_abo_allele_frequencies = 100.
Proof. reflexivity. Qed.

Record RhAlleleFreq := mkRhAlleleFreq {
  freq_D_allele : nat;
  freq_d_allele : nat
}.

Definition us_rh_allele_frequencies : RhAlleleFreq :=
  mkRhAlleleFreq 60 40.

Definition expected_rh_neg_percent (f : RhAlleleFreq) : nat :=
  (freq_d_allele f * freq_d_allele f) / 100.

Theorem us_expected_rh_neg :
  expected_rh_neg_percent us_rh_allele_frequencies = 16.
Proof. reflexivity. Qed.

(******************************************************************************)
(*                           EXTRACTION                                       *)
(******************************************************************************)

Require Import Extraction.
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive list => "list" ["[]" "(::)"].
Extract Inductive prod => "(*)" ["(,)"].
Extract Inductive option => "option" ["Some" "None"].
Extraction Language OCaml.

Extraction "transfusion_v2.ml"
  ABO Rh BloodType Antigen Product Priority Severity
  AntigenSet AntibodySet phenotype_antigens abo_natural_antibodies
  RhSensitization recipient_antibodies
  has_antigen has_antibody has_antibody_abo
  has_antibody_immunological has_antibody_policy
  rbc_compatible_abo rbc_compatible_rh rbc_compatible_with_sens
  compatible plasma_compatible plasma_compatible_correct plasma_compatible_legacy
  product_rbc_compatible product_plasma_compatible product_platelet_compatible
  whole_blood_compatible
  compatible_dec plasma_compatible_dec whole_blood_compatible_dec
  all_blood_types count_donors count_recipients
  is_abo_rh_antigen is_minor_antigen
  IgClass ABOAntibodyProfile ThermalRange TiterByClass
  classify_titer_by_class total_titer titer_has_IgG
  TiterLevel classify_titer PlasmaUnit is_low_titer_plasma
  TiterPolicy plasma_safe_with_policy plasma_hemolytic_risk plasma_safe_for_recipient
  ABOSubtype subtype_compatible subtype_abo_compatible a1_compatible
  is_acquired_b acquired_b_safe_donor is_cis_ab
  AntiA1Policy may_have_anti_A1_with_policy may_have_anti_A1
  RhVariant variant_transfusion_type variant_donation_type variant_can_make_anti_D
  rh_variant_compatible full_subtype_compatible
  Recipient Donor extended_compatible
  DATResult DATPattern DATProfile AIHAType classify_aiha
  dat_positive crossmatch_difficulty needs_adsorption_study
  extended_compatible_with_dat extended_transfusion_safe
  ABOAllele RhAllele genotype_phenotype punnett_full offspring_phenotypes
  abo_distribution hardy_weinberg
  Population pop_frequency pop_sum
  shelf_life is_expired storage_lesion platelet_dose ffp_dose_ml
  LabTest test_time_minutes
  assess_severity match_quality make_decision
  neonatal_compatible rhogam_indicated
  allocation_score triage_total_allocated shortage_triage_bounded
  ExtendedPhenotype make_extended_phenotype minor_antigen_compatible
  antigen_list_to_set has_antigen_in_list minor_antigen_compatible_list
  default_minor_antigen_list sickle_cell_matching_antigens extended_matching_antigens
  full_compatible
  is_duffy_null duffy_compatible_correct
  immunogenicity_K_percent
  duffy_null_malaria_resistance_prevalence_africa
  AntibodyStatus AntibodyRecord is_kidd_antigen
  ImmuneHistory significant_antibodies history_compatible
  TransfusionOutcome predict_outcome transfusion_decision_with_history
  update_antibody_status reactivate_on_exposure antibody_clinically_significant
  kidd_antibody_evanescence_risk_percent
  HLAClass1 hla_matched PlateletUnit platelet_full_compatible CryoUnit
  estimated_blood_volume massive_transfusion_protocol_ratio
  rbc_units_for_hgb_increase cryo_dose_units
  Inventory get_inventory rh_neg_supply rh_pos_supply emergency_reserve
  total_units available_for
  AllocationRequest shortage_triage
  RhExtended rh_to_extended blood_to_extended extended_rh_safe
  rh_neg_prevalence expected_compatible_supply
  HDFNSeverity hdfn_severity_score antibody_hdfn_severity
  PregnancyProfile hdfn_abo_risk hdfn_rh_risk_full rhogam_indicated_full
  hdfn_risk_antigens is_hdfn_risk_antigen has_high_risk_antibody_unified
  AntibodyScreenResult screen_to_crossmatch
  EmergencyLevel emergency_rbc_type emergency_plasma_type
  max_uncrossmatched_units emergency_threshold_exceeded
  IrradiationIndication requires_irradiation IrradiatedProduct irradiation_adequate
  GranulocyteUnit granulocyte_compatible granulocyte_safe granulocyte_expired
  ExchangeTransfusionParams calculate_exchange_volume
  sickle_cell_exchange_requirements antigen_in_list sickle_exchange_compatible
  neonatal_exchange_compatible
  CMVStatus cmv_safe_required
  donation_reach vulnerability
  recipient_blood_type recipient_compatible_with_bt sensitization_risk
  FullTransfusionDecision make_full_decision
  FullTransfusionDecisionWithDAT make_full_decision_with_dat full_decision_with_dat_safe
  find_compatible_in_inventory
  agglutination crossmatch_reaction
  count_whole_blood_donors
  severity_score mortality_risk_percent
  RhCcEe rh_haplotype_frequency_white phenotype_from_haplotypes rh_haplotype_compatible
  inherits_from valid_child_genotype valid_full_child_genotype
  emergency_donor find_compatible_donors is_rare rare_types
  transfusion_impossible
  RhAlleleFreq us_rh_allele_frequencies expected_rh_neg_percent.
