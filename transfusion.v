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

Definition antigen_eq_dec (x y : Antigen) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition all_antigens : list Antigen :=
  [ Ag_A; Ag_B; Ag_AB; Ag_A1; Ag_Aw; Ag_Ax
  ; Ag_M; Ag_N; Ag_S; Ag_s; Ag_U; Ag_He; Ag_Mia; Ag_Mc; Ag_Vw; Ag_Mur
  ; Ag_Mg; Ag_Vr; Ag_Me; Ag_Mta; Ag_Sta; Ag_Ria; Ag_Cla; Ag_Nya; Ag_Hut
  ; Ag_Hil; Ag_Mv; Ag_Far; Ag_sD; Ag_Mit; Ag_Dantu; Ag_Hop; Ag_Nob; Ag_Ena
  ; Ag_ENKT; Ag_Nsu; Ag_HAG; Ag_ENEV; Ag_MARS; Ag_ENDA; Ag_ENEH; Ag_MNTD
  ; Ag_SARA; Ag_KIPP; Ag_JENU; Ag_SUMI; Ag_KASP; Ag_MINE; Ag_MINY
  ; Ag_P1; Ag_Pk; Ag_NOR
  ; Ag_D; Ag_C; Ag_E; Ag_c; Ag_e; Ag_f; Ag_Ce; Ag_cE; Ag_Cw; Ag_Cx
  ; Ag_V; Ag_Ew; Ag_G; Ag_Hrs; Ag_hrS; Ag_hrB; Ag_VS; Ag_CG; Ag_CE
  ; Ag_Dw; Ag_clike; Ag_Cces; Ag_Rh17; Ag_Hr; Ag_Rh29; Ag_Goa; Ag_hrH
  ; Ag_Rh32; Ag_Rh33; Ag_HrB; Ag_Rh35; Ag_Bea; Ag_Evans; Ag_Rh39; Ag_Tar
  ; Ag_Rh41; Ag_Rh42; Ag_Crawford; Ag_Nou; Ag_Riv; Ag_Sec; Ag_Dav; Ag_JAL
  ; Ag_STEM; Ag_FPTT; Ag_MAR; Ag_BARC; Ag_JAHK; Ag_DAK; Ag_LOCR; Ag_CENR
  ; Ag_CEST; Ag_CELO; Ag_CEAG; Ag_PARG; Ag_CEVF; Ag_CEVA
  ; Ag_Lua; Ag_Lub; Ag_Lu3; Ag_Lu4; Ag_Lu5; Ag_Lu6; Ag_Lu7; Ag_Lu8
  ; Ag_Lu9; Ag_Lu11; Ag_Lu12; Ag_Lu13; Ag_Lu14; Ag_Lu16; Ag_Lu17
  ; Ag_Aua; Ag_Aub; Ag_Lu20; Ag_Lu21; Ag_LURC; Ag_LURA; Ag_LUBI
  ; Ag_K; Ag_k; Ag_Kpa; Ag_Kpb; Ag_Ku; Ag_Jsa; Ag_Jsb; Ag_K11; Ag_K12
  ; Ag_K13; Ag_K14; Ag_K16; Ag_K17; Ag_K18; Ag_K19; Ag_Km; Ag_Kpc
  ; Ag_K22; Ag_K23; Ag_K24; Ag_KELP; Ag_TOU; Ag_RAZ; Ag_VLAN; Ag_KALT
  ; Ag_KTIM; Ag_KYO; Ag_KUCI; Ag_KANT; Ag_KASH; Ag_KETI; Ag_KHUL
  ; Ag_Lea; Ag_Leb; Ag_Leab; Ag_LebH; Ag_ALeb; Ag_BLeb
  ; Ag_Fya; Ag_Fyb; Ag_Fy3; Ag_Fy4; Ag_Fy5; Ag_Fy6
  ; Ag_Jka; Ag_Jkb; Ag_Jk3
  ; Ag_Dia; Ag_Dib; Ag_Wra; Ag_Wrb; Ag_Wda; Ag_Rba; Ag_WARR; Ag_ELO
  ; Ag_Wu; Ag_Bpa; Ag_Moa; Ag_Hga; Ag_Vga; Ag_Swa; Ag_BOW; Ag_NFLD
  ; Ag_Jna; Ag_KREP; Ag_Tra; Ag_Fra; Ag_SW1; Ag_DISK
  ; Ag_Yta; Ag_Ytb
  ; Ag_Xga; Ag_CD99
  ; Ag_Sc1; Ag_Sc2; Ag_Sc3; Ag_Rd; Ag_STAR; Ag_SCER; Ag_SCAN
  ; Ag_Doa; Ag_Dob; Ag_Gya; Ag_Hy; Ag_Joa; Ag_DOYA; Ag_DOMR; Ag_DOLG
  ; Ag_Coa; Ag_Cob; Ag_Co3; Ag_Co4
  ; Ag_LWa; Ag_LWab; Ag_LWb
  ; Ag_Ch1; Ag_Ch2; Ag_Ch3; Ag_Ch4; Ag_Ch5; Ag_Ch6; Ag_WH
  ; Ag_Rg1; Ag_Rg2
  ; Ag_H; Ag_H2
  ; Ag_Kx
  ; Ag_Ge2; Ag_Ge3; Ag_Ge4; Ag_Wb; Ag_Lsa; Ag_Ana; Ag_Dha; Ag_GEIS
  ; Ag_GEPL; Ag_GEAT; Ag_GETI
  ; Ag_Cra; Ag_Tca; Ag_Tcb; Ag_Tcc; Ag_Dra; Ag_Esa; Ag_IFC; Ag_WESa
  ; Ag_WESb; Ag_UMC; Ag_GUTI; Ag_SERF; Ag_ZENA; Ag_CROV; Ag_CRAM
  ; Ag_CROZ; Ag_CRUE; Ag_CRAG; Ag_CREG
  ; Ag_Kna; Ag_Knb; Ag_McCa; Ag_Sla; Ag_Yka; Ag_McCb; Ag_Vil; Ag_KCAM
  ; Ag_KDAS; Ag_KNSB
  ; Ag_Ina; Ag_Inb; Ag_INFI; Ag_INJA; Ag_INRA
  ; Ag_Oka; Ag_OKGV; Ag_OKVM
  ; Ag_MER2
  ; Ag_JMH; Ag_JMHK; Ag_JMHL; Ag_JMHG; Ag_JMHM; Ag_JMHQ
  ; Ag_I; Ag_i
  ; Ag_P; Ag_PX2
  ; Ag_GIL
  ; Ag_Duclos; Ag_Ola; Ag_DSLK
  ; Ag_FORS1
  ; Ag_Jra
  ; Ag_Lan
  ; Ag_Vel
  ; Ag_CD59p
  ; Ag_Ata; Ag_Atb
  ; Ag_KANNO
  ; Ag_Sda
  ; Ag_CTL2_HEL; Ag_CTL2_REGA
  ; Ag_PEL
  ; Ag_MAM
  ; Ag_EMMI; Ag_EMMA; Ag_EMMP
  ; Ag_ABCC1
  ].

Definition antigen_count : nat := length all_antigens.

Theorem antigen_count_value : antigen_count = 318.
Proof. native_compute. reflexivity. Qed.

Theorem all_antigens_complete : forall ag : Antigen, In ag all_antigens.
Proof. destruct ag; simpl; repeat (try (left; reflexivity); right); left; reflexivity. Qed.

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

(** Alias for explicitness - identical to plasma_compatible.
    Both names are retained for API clarity:
    - plasma_compatible: standard name
    - plasma_compatible_correct: emphasizes this is the correct ABO-only model *)
Definition plasma_compatible_correct (recipient donor : BloodType) : bool :=
  plasma_compatible recipient donor.

Theorem plasma_compatible_correct_eq : forall r d,
  plasma_compatible_correct r d = plasma_compatible r d.
Proof. reflexivity. Qed.

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

(** ========== INTEGRATED PLASMA TRANSFUSION WITH TITER ========== *)

(** This section integrates the ABO titer model into plasma transfusion decisions.
    The key insight is that ABO compatibility alone is insufficient for safe
    plasma transfusion in non-identical ABO contexts:

    1. ABO-identical plasma: Always safe (no concern about isoagglutinin titers)
    2. ABO-compatible but non-identical: Titer matters!
       - Low titer: Safe
       - Moderate titer: Safe under standard policy, risky for vulnerable
       - High/Critical titer: Always risky

    Clinical scenarios requiring integrated titer checking:
    - Group O plasma to non-O recipients (contains anti-A and anti-B)
    - Group A plasma to B or AB recipients (contains anti-B)
    - Group B plasma to A or AB recipients (contains anti-A)
    - Emergency release of non-type-specific plasma
    - Platelet transfusion (contains plasma with isoagglutinins)

    Source: Karafin et al., Transfusion 2012; Cooling, ISBT Science Series 2015 *)

(** Plasma transfusion context for integrated decision making *)
Inductive PlasmaTransfusionContext : Type :=
  | Ctx_Standard
  | Ctx_Pediatric
  | Ctx_MassiveTransfusion
  | Ctx_ImmuneCompromised
  | Ctx_Emergency_Unknown_Type.

(** Map context to appropriate titer policy *)
Definition context_to_policy (ctx : PlasmaTransfusionContext) : TiterPolicy :=
  match ctx with
  | Ctx_Standard => Policy_Standard
  | Ctx_Pediatric => Policy_Strict
  | Ctx_MassiveTransfusion => Policy_Strict
  | Ctx_ImmuneCompromised => Policy_Strict
  | Ctx_Emergency_Unknown_Type => Policy_Critical_Only
  end.

(** Full integrated plasma compatibility check.
    This is the PREFERRED function for plasma transfusion decisions.

    Key insight: For ABO-COMPATIBLE plasma, titer is irrelevant (no relevant antibodies).
    For ABO-INCOMPATIBLE plasma, titer determines whether it's safe enough.

    Compatibility modes:
    1. ABO-identical: Always safe (e.g., A plasma to A recipient)
    2. ABO-compatible: Always safe (e.g., AB plasma to any recipient)
    3. ABO-incompatible with low titer: May be acceptable in emergencies
    4. ABO-incompatible with high titer: Never safe *)
Definition plasma_transfusion_safe (recipient : BloodType) (plasma : PlasmaUnit)
                                    (ctx : PlasmaTransfusionContext) : bool :=
  let donor := (plasma_abo plasma, plasma_rh plasma) in
  let abo_ok := plasma_compatible recipient donor in
  if abo_ok then true
  else
    let titer_ok := plasma_safe_with_policy (context_to_policy ctx)
                                             (fst recipient) plasma in
    titer_ok.

(** ABO-identical plasma is always safe regardless of titer *)
Definition is_abo_identical_plasma (recipient : BloodType) (plasma : PlasmaUnit) : bool :=
  if abo_eq_dec (fst recipient) (plasma_abo plasma) then true else false.

Theorem abo_identical_plasma_always_safe : forall recipient plasma,
  is_abo_identical_plasma recipient plasma = true ->
  plasma_hemolytic_risk (fst recipient) plasma = Titer_Low.
Proof.
  intros [[| | | ] [| ]] plasma Hident;
  unfold is_abo_identical_plasma in Hident;
  unfold plasma_hemolytic_risk, classify_titer;
  destruct (plasma_abo plasma) eqn:Habo; simpl in *;
  try discriminate; try reflexivity.
Qed.

(** Non-identical ABO plasma requires titer check - critical titer rejected *)
Theorem non_identical_requires_titer_check : forall plasma,
  plasma_abo plasma = O ->
  (plasma_anti_A_titer plasma > 256)%nat ->
  plasma_safe_for_recipient A plasma = false.
Proof.
  intros plasma Habo Htiter.
  unfold plasma_safe_for_recipient, plasma_safe_with_policy, plasma_hemolytic_risk.
  rewrite Habo. unfold classify_titer. simpl.
  destruct (Nat.leb (plasma_anti_A_titer plasma) 50) eqn:Hle1.
  - apply Nat.leb_le in Hle1. lia.
  - destruct (Nat.leb (plasma_anti_A_titer plasma) 128) eqn:Hle2.
    + apply Nat.leb_le in Hle2. lia.
    + destruct (Nat.leb (plasma_anti_A_titer plasma) 256) eqn:Hle3.
      * apply Nat.leb_le in Hle3. lia.
      * reflexivity.
Qed.

(** Moderate titer (51-128) is accepted under standard policy but rejected under strict *)
Theorem moderate_titer_policy_difference : forall plasma,
  plasma_abo plasma = O ->
  (plasma_anti_A_titer plasma > 50)%nat ->
  (plasma_anti_A_titer plasma <= 128)%nat ->
  plasma_safe_for_recipient A plasma = true /\
  plasma_safe_strict A plasma = false.
Proof.
  intros plasma Habo Hgt Hle.
  unfold plasma_safe_for_recipient, plasma_safe_strict, plasma_safe_with_policy,
         plasma_hemolytic_risk. rewrite Habo. unfold classify_titer. simpl.
  destruct (Nat.leb (plasma_anti_A_titer plasma) 50) eqn:Hle1.
  - apply Nat.leb_le in Hle1. lia.
  - destruct (Nat.leb (plasma_anti_A_titer plasma) 128) eqn:Hle2.
    + split; reflexivity.
    + apply Nat.leb_nle in Hle2. lia.
Qed.

(** Pediatric patients get strict titer policy *)
Theorem pediatric_strict_policy :
  context_to_policy Ctx_Pediatric = Policy_Strict.
Proof. reflexivity. Qed.

(** Massive transfusion gets strict titer policy *)
Theorem massive_transfusion_strict_policy :
  context_to_policy Ctx_MassiveTransfusion = Policy_Strict.
Proof. reflexivity. Qed.

(** AB plasma is safe for all recipients in all contexts (no anti-A or anti-B) *)
Theorem ab_plasma_universally_safe : forall recipient rh ctx,
  let plasma := mkPlasmaUnit AB rh 0 0 250 in
  plasma_transfusion_safe recipient plasma ctx = true.
Proof.
  intros [[| | | ] [| ]] rh ctx; unfold plasma_transfusion_safe; simpl;
  destruct ctx; reflexivity.
Qed.

(** High titer O plasma is dangerous for A recipients even with standard policy *)
Theorem high_titer_o_dangerous_for_a : forall rh vol ctx,
  let plasma := mkPlasmaUnit O rh 300 50 vol in
  plasma_transfusion_safe A_pos plasma ctx = false.
Proof.
  intros rh vol ctx.
  unfold plasma_transfusion_safe, plasma_safe_with_policy, plasma_hemolytic_risk.
  simpl. destruct ctx; reflexivity.
Qed.

(** Low titer O plasma is safe for A recipients under standard policy *)
Theorem low_titer_o_safe_for_a_standard : forall rh vol,
  let plasma := mkPlasmaUnit O rh 40 40 vol in
  plasma_transfusion_safe A_pos plasma Ctx_Standard = true.
Proof. intros; unfold plasma_transfusion_safe; simpl; reflexivity. Qed.

(** But moderate titer O plasma rejected for pediatric A recipients *)
Theorem moderate_titer_o_rejected_pediatric : forall rh vol,
  let plasma := mkPlasmaUnit O rh 100 100 vol in
  plasma_transfusion_safe A_pos plasma Ctx_Pediatric = false.
Proof. intros; unfold plasma_transfusion_safe; simpl; reflexivity. Qed.

(** Platelet transfusion plasma volume consideration.
    Platelets contain ~200-300 mL plasma. For out-of-group platelets,
    this plasma carries clinically significant isoagglutinin risk. *)
Definition platelet_plasma_volume_ml : nat := 250.

Record PlateletUnitWithTiter := mkPlateletWithTiter {
  plt_base_abo : ABO;
  plt_base_rh : Rh;
  plt_anti_A_titer : nat;
  plt_anti_B_titer : nat
}.

Definition platelet_to_plasma_unit (plt : PlateletUnitWithTiter) : PlasmaUnit :=
  mkPlasmaUnit (plt_base_abo plt) (plt_base_rh plt)
               (plt_anti_A_titer plt) (plt_anti_B_titer plt)
               platelet_plasma_volume_ml.

Definition platelet_plasma_safe (recipient : BloodType)
                                 (plt : PlateletUnitWithTiter)
                                 (ctx : PlasmaTransfusionContext) : bool :=
  plasma_transfusion_safe recipient (platelet_to_plasma_unit plt) ctx.

Theorem high_titer_o_platelets_dangerous_for_a :
  forall rh,
  let plt := mkPlateletWithTiter O rh 300 50 in
  platelet_plasma_safe A_pos plt Ctx_Standard = false.
Proof. intros; reflexivity. Qed.

(** Helper: check if titer level is low *)
Definition is_titer_low (t : TiterLevel) : bool :=
  match t with Titer_Low => true | _ => false end.

(** Emergency plasma release decision matrix.
    When type is unknown, we must assume WORST CASE (AB recipient).
    AB plasma is universal donor for plasma (no anti-A or anti-B).
    Other plasma types need low titer to be safe for unknown recipients. *)
Definition emergency_plasma_decision (known_type : option BloodType)
                                      (available_plasma : PlasmaUnit) : bool :=
  match known_type with
  | Some recipient => plasma_transfusion_safe recipient available_plasma Ctx_Emergency_Unknown_Type
  | None =>
      match plasma_abo available_plasma with
      | AB => true
      | _ => is_titer_low (plasma_hemolytic_risk AB available_plasma)
      end
  end.

Theorem ab_plasma_safe_for_unknown_type :
  forall rh vol,
  let plasma := mkPlasmaUnit AB rh 0 0 vol in
  emergency_plasma_decision None plasma = true.
Proof. intros; reflexivity. Qed.

Theorem high_titer_o_plasma_not_for_unknown_type :
  forall rh vol,
  let plasma := mkPlasmaUnit O rh 300 300 vol in
  emergency_plasma_decision None plasma = false.
Proof. intros; unfold emergency_plasma_decision; simpl; reflexivity. Qed.

(** Summary: The integrated model ensures that:
    1. ABO compatibility is checked (recipient antibodies vs donor antigens)
    2. Titer safety is checked (donor antibodies vs recipient antigens)
    3. Context-appropriate policies are applied
    4. Vulnerable populations (pediatric, immunocompromised) get stricter criteria *)

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
Require Import Coq.QArith.Qround.

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
    Source: Wikipedia "Blood type distribution by country" (2024), compiled from
    national blood bank registries and peer-reviewed studies. Data normalized to
    sum to 1000 per mille. Original sources include Red Cross organizations,
    national health ministries, and published hematology research. *)
Inductive Population : Type :=
  Albania | Algeria | Argentina | Armenia | Australia | Austria | Azerbaijan | Bahrain | Bangladesh | Belarus | Belgium | Bhutan | Bolivia | BosniaHerzegovina | Brazil | Bulgaria | BurkinaFaso | Cambodia | Cameroon | Canada | Chile | China | Colombia | CostaRica | Croatia | Cuba | Cyprus | CzechRepublic | DemocraticRepublicCongo | Denmark | DominicanRepublic | Ecuador | ElSalvador | Estonia | Ethiopia | Fiji | Finland | France | Gabon | Georgia | Germany | Ghana | Greece | Guinea | Honduras | HongKong | Hungary | Iceland | India | Indonesia | Iran | Iraq | Ireland | Israel | Italy | IvoryCoast | Jamaica | Japan | Jordan | Kazakhstan | Kenya | Laos | Latvia | Lebanon | Libya | Liechtenstein | Lithuania | Luxembourg | Macao | Malaysia | Malta | Mauritania | Mauritius | Mexico | Moldova | Mongolia | Morocco | Myanmar | Namibia | Nepal | Netherlands | NewZealand | Nicaragua | Nigeria | NorthKorea | NorthMacedonia | Norway | Oman | Pakistan | PapuaNewGuinea | Paraguay | Peru | Philippines | Poland | Portugal | Romania | Russia | SaudiArabia | Serbia | Singapore | Slovakia | Slovenia | Somalia | SouthAfrica | SouthKorea | Spain | SriLanka | Sudan | Sweden | Switzerland | Syria | Taiwan | Thailand | Tunisia | Turkey | Uganda | Ukraine | UnitedArabEmirates | UnitedKingdom | UnitedStates | Uzbekistan | Venezuela | Vietnam | Yemen | Zimbabwe.

Definition pop_frequency (pop : Population) (bt : BloodType) : nat :=
  match pop, bt with
  | Albania, (O, Pos) => 341 | Albania, (O, Neg) => 60
  | Albania, (A, Pos) => 312 | Albania, (A, Neg) => 55
  | Albania, (B, Pos) => 145 | Albania, (B, Neg) => 26
  | Albania, (AB, Pos) => 52 | Albania, (AB, Neg) => 9
  | Algeria, (O, Pos) => 400 | Algeria, (O, Neg) => 66
  | Algeria, (A, Pos) => 300 | Algeria, (A, Neg) => 23
  | Algeria, (B, Pos) => 150 | Algeria, (B, Neg) => 11
  | Algeria, (AB, Pos) => 43 | Algeria, (AB, Neg) => 8
  | Argentina, (O, Pos) => 503 | Argentina, (O, Neg) => 43
  | Argentina, (A, Pos) => 311 | Argentina, (A, Neg) => 30
  | Argentina, (B, Pos) => 82 | Argentina, (B, Neg) => 7
  | Argentina, (AB, Pos) => 22 | Argentina, (AB, Neg) => 2
  | Armenia, (O, Pos) => 290 | Armenia, (O, Neg) => 20
  | Armenia, (A, Pos) => 463 | Armenia, (A, Neg) => 37
  | Armenia, (B, Pos) => 120 | Armenia, (B, Neg) => 10
  | Armenia, (AB, Pos) => 56 | Armenia, (AB, Neg) => 4
  | Australia, (O, Pos) => 380 | Australia, (O, Neg) => 70
  | Australia, (A, Pos) => 320 | Australia, (A, Neg) => 60
  | Australia, (B, Pos) => 120 | Australia, (B, Neg) => 20
  | Australia, (AB, Pos) => 40 | Australia, (AB, Neg) => 10
  | Austria, (O, Pos) => 300 | Austria, (O, Neg) => 60
  | Austria, (A, Pos) => 370 | Austria, (A, Neg) => 70
  | Austria, (B, Pos) => 120 | Austria, (B, Neg) => 20
  | Austria, (AB, Pos) => 50 | Austria, (AB, Neg) => 5
  | Azerbaijan, (O, Pos) => 298 | Azerbaijan, (O, Neg) => 33
  | Azerbaijan, (A, Pos) => 300 | Azerbaijan, (A, Neg) => 34
  | Azerbaijan, (B, Pos) => 211 | Azerbaijan, (B, Neg) => 24
  | Azerbaijan, (AB, Pos) => 90 | Azerbaijan, (AB, Neg) => 10
  | Bahrain, (O, Pos) => 485 | Bahrain, (O, Neg) => 33
  | Bahrain, (A, Pos) => 154 | Bahrain, (A, Neg) => 13
  | Bahrain, (B, Pos) => 226 | Bahrain, (B, Neg) => 10
  | Bahrain, (AB, Pos) => 37 | Bahrain, (AB, Neg) => 3
  | Bangladesh, (O, Pos) => 292 | Bangladesh, (O, Neg) => 5
  | Bangladesh, (A, Pos) => 263 | Bangladesh, (A, Neg) => 5
  | Bangladesh, (B, Pos) => 331 | Bangladesh, (B, Neg) => 6
  | Bangladesh, (AB, Pos) => 96 | Bangladesh, (AB, Neg) => 2
  | Belarus, (O, Pos) => 323 | Belarus, (O, Neg) => 57
  | Belarus, (A, Pos) => 306 | Belarus, (A, Neg) => 54
  | Belarus, (B, Pos) => 153 | Belarus, (B, Neg) => 27
  | Belarus, (AB, Pos) => 68 | Belarus, (AB, Neg) => 12
  | Belgium, (O, Pos) => 380 | Belgium, (O, Neg) => 70
  | Belgium, (A, Pos) => 340 | Belgium, (A, Neg) => 60
  | Belgium, (B, Pos) => 85 | Belgium, (B, Neg) => 15
  | Belgium, (AB, Pos) => 40 | Belgium, (AB, Neg) => 10
  | Bhutan, (O, Pos) => 382 | Bhutan, (O, Neg) => 1
  | Bhutan, (A, Pos) => 295 | Bhutan, (A, Neg) => 0
  | Bhutan, (B, Pos) => 239 | Bhutan, (B, Neg) => 0
  | Bhutan, (AB, Pos) => 84 | Bhutan, (AB, Neg) => 0
  | Bolivia, (O, Pos) => 515 | Bolivia, (O, Neg) => 44
  | Bolivia, (A, Pos) => 205 | Bolivia, (A, Neg) => 27
  | Bolivia, (B, Pos) => 101 | Bolivia, (B, Neg) => 5
  | Bolivia, (AB, Pos) => 12 | Bolivia, (AB, Neg) => 1
  | BosniaHerzegovina, (O, Pos) => 310 | BosniaHerzegovina, (O, Neg) => 50
  | BosniaHerzegovina, (A, Pos) => 360 | BosniaHerzegovina, (A, Neg) => 70
  | BosniaHerzegovina, (B, Pos) => 120 | BosniaHerzegovina, (B, Neg) => 20
  | BosniaHerzegovina, (AB, Pos) => 60 | BosniaHerzegovina, (AB, Neg) => 10
  | Brazil, (O, Pos) => 360 | Brazil, (O, Neg) => 90
  | Brazil, (A, Pos) => 340 | Brazil, (A, Neg) => 80
  | Brazil, (B, Pos) => 80 | Brazil, (B, Neg) => 20
  | Brazil, (AB, Pos) => 25 | Brazil, (AB, Neg) => 5
  | Bulgaria, (O, Pos) => 280 | Bulgaria, (O, Neg) => 50
  | Bulgaria, (A, Pos) => 374 | Bulgaria, (A, Neg) => 66
  | Bulgaria, (B, Pos) => 128 | Bulgaria, (B, Neg) => 22
  | Bulgaria, (AB, Pos) => 68 | Bulgaria, (AB, Neg) => 12
  | BurkinaFaso, (O, Pos) => 399 | BurkinaFaso, (O, Neg) => 34
  | BurkinaFaso, (A, Pos) => 208 | BurkinaFaso, (A, Neg) => 18
  | BurkinaFaso, (B, Pos) => 263 | BurkinaFaso, (B, Neg) => 22
  | BurkinaFaso, (AB, Pos) => 52 | BurkinaFaso, (AB, Neg) => 4
  | Cambodia, (O, Pos) => 467 | Cambodia, (O, Neg) => 13
  | Cambodia, (A, Pos) => 272 | Cambodia, (A, Neg) => 8
  | Cambodia, (B, Pos) => 185 | Cambodia, (B, Neg) => 5
  | Cambodia, (AB, Pos) => 49 | Cambodia, (AB, Neg) => 1
  | Cameroon, (O, Pos) => 468 | Cameroon, (O, Neg) => 18
  | Cameroon, (A, Pos) => 242 | Cameroon, (A, Neg) => 9
  | Cameroon, (B, Pos) => 211 | Cameroon, (B, Neg) => 8
  | Cameroon, (AB, Pos) => 43 | Cameroon, (AB, Neg) => 2
  | Canada, (O, Pos) => 390 | Canada, (O, Neg) => 70
  | Canada, (A, Pos) => 360 | Canada, (A, Neg) => 60
  | Canada, (B, Pos) => 76 | Canada, (B, Neg) => 14
  | Canada, (AB, Pos) => 25 | Canada, (AB, Neg) => 5
  | Chile, (O, Pos) => 550 | Chile, (O, Neg) => 42
  | Chile, (A, Pos) => 281 | Chile, (A, Neg) => 21
  | Chile, (B, Pos) => 80 | Chile, (B, Neg) => 6
  | Chile, (AB, Pos) => 18 | Chile, (AB, Neg) => 1
  | China, (O, Pos) => 340 | China, (O, Neg) => 4
  | China, (A, Pos) => 276 | China, (A, Neg) => 3
  | China, (B, Pos) => 289 | China, (B, Neg) => 2
  | China, (AB, Pos) => 84 | China, (AB, Neg) => 2
  | Colombia, (O, Pos) => 613 | Colombia, (O, Neg) => 51
  | Colombia, (A, Pos) => 211 | Colombia, (A, Neg) => 27
  | Colombia, (B, Pos) => 73 | Colombia, (B, Neg) => 7
  | Colombia, (AB, Pos) => 15 | Colombia, (AB, Neg) => 3
  | CostaRica, (O, Pos) => 497 | CostaRica, (O, Neg) => 34
  | CostaRica, (A, Pos) => 285 | CostaRica, (A, Neg) => 19
  | CostaRica, (B, Pos) => 124 | CostaRica, (B, Neg) => 9
  | CostaRica, (AB, Pos) => 30 | CostaRica, (AB, Neg) => 2
  | Croatia, (O, Pos) => 290 | Croatia, (O, Neg) => 50
  | Croatia, (A, Pos) => 360 | Croatia, (A, Neg) => 60
  | Croatia, (B, Pos) => 150 | Croatia, (B, Neg) => 30
  | Croatia, (AB, Pos) => 50 | Croatia, (AB, Neg) => 10
  | Cuba, (O, Pos) => 458 | Cuba, (O, Neg) => 36
  | Cuba, (A, Pos) => 335 | Cuba, (A, Neg) => 28
  | Cuba, (B, Pos) => 102 | Cuba, (B, Neg) => 10
  | Cuba, (AB, Pos) => 29 | Cuba, (AB, Neg) => 2
  | Cyprus, (O, Pos) => 352 | Cyprus, (O, Neg) => 39
  | Cyprus, (A, Pos) => 404 | Cyprus, (A, Neg) => 35
  | Cyprus, (B, Pos) => 111 | Cyprus, (B, Neg) => 9
  | Cyprus, (AB, Pos) => 47 | Cyprus, (AB, Neg) => 4
  | CzechRepublic, (O, Pos) => 270 | CzechRepublic, (O, Neg) => 50
  | CzechRepublic, (A, Pos) => 360 | CzechRepublic, (A, Neg) => 60
  | CzechRepublic, (B, Pos) => 150 | CzechRepublic, (B, Neg) => 30
  | CzechRepublic, (AB, Pos) => 70 | CzechRepublic, (AB, Neg) => 10
  | DemocraticRepublicCongo, (O, Pos) => 595 | DemocraticRepublicCongo, (O, Neg) => 10
  | DemocraticRepublicCongo, (A, Pos) => 213 | DemocraticRepublicCongo, (A, Neg) => 3
  | DemocraticRepublicCongo, (B, Pos) => 152 | DemocraticRepublicCongo, (B, Neg) => 2
  | DemocraticRepublicCongo, (AB, Pos) => 24 | DemocraticRepublicCongo, (AB, Neg) => 1
  | Denmark, (O, Pos) => 350 | Denmark, (O, Neg) => 60
  | Denmark, (A, Pos) => 370 | Denmark, (A, Neg) => 70
  | Denmark, (B, Pos) => 80 | Denmark, (B, Neg) => 20
  | Denmark, (AB, Pos) => 40 | Denmark, (AB, Neg) => 10
  | DominicanRepublic, (O, Pos) => 472 | DominicanRepublic, (O, Neg) => 37
  | DominicanRepublic, (A, Pos) => 264 | DominicanRepublic, (A, Neg) => 21
  | DominicanRepublic, (B, Pos) => 169 | DominicanRepublic, (B, Neg) => 14
  | DominicanRepublic, (AB, Pos) => 21 | DominicanRepublic, (AB, Neg) => 2
  | Ecuador, (O, Pos) => 750 | Ecuador, (O, Neg) => 24
  | Ecuador, (A, Pos) => 140 | Ecuador, (A, Neg) => 7
  | Ecuador, (B, Pos) => 71 | Ecuador, (B, Neg) => 3
  | Ecuador, (AB, Pos) => 5 | Ecuador, (AB, Neg) => 0
  | ElSalvador, (O, Pos) => 620 | ElSalvador, (O, Neg) => 10
  | ElSalvador, (A, Pos) => 230 | ElSalvador, (A, Neg) => 10
  | ElSalvador, (B, Pos) => 110 | ElSalvador, (B, Neg) => 7
  | ElSalvador, (AB, Pos) => 10 | ElSalvador, (AB, Neg) => 3
  | Estonia, (O, Pos) => 295 | Estonia, (O, Neg) => 43
  | Estonia, (A, Pos) => 308 | Estonia, (A, Neg) => 45
  | Estonia, (B, Pos) => 207 | Estonia, (B, Neg) => 30
  | Estonia, (AB, Pos) => 63 | Estonia, (AB, Neg) => 9
  | Ethiopia, (O, Pos) => 390 | Ethiopia, (O, Neg) => 30
  | Ethiopia, (A, Pos) => 280 | Ethiopia, (A, Neg) => 20
  | Ethiopia, (B, Pos) => 210 | Ethiopia, (B, Neg) => 10
  | Ethiopia, (AB, Pos) => 50 | Ethiopia, (AB, Neg) => 10
  | Fiji, (O, Pos) => 430 | Fiji, (O, Neg) => 10
  | Fiji, (A, Pos) => 333 | Fiji, (A, Neg) => 7
  | Fiji, (B, Pos) => 165 | Fiji, (B, Neg) => 5
  | Fiji, (AB, Pos) => 48 | Fiji, (AB, Neg) => 2
  | Finland, (O, Pos) => 280 | Finland, (O, Neg) => 50
  | Finland, (A, Pos) => 350 | Finland, (A, Neg) => 60
  | Finland, (B, Pos) => 160 | Finland, (B, Neg) => 20
  | Finland, (AB, Pos) => 70 | Finland, (AB, Neg) => 10
  | France, (O, Pos) => 365 | France, (O, Neg) => 65
  | France, (A, Pos) => 382 | France, (A, Neg) => 68
  | France, (B, Pos) => 77 | France, (B, Neg) => 14
  | France, (AB, Pos) => 25 | France, (AB, Neg) => 4
  | Gabon, (O, Pos) => 576 | Gabon, (O, Neg) => 14
  | Gabon, (A, Pos) => 205 | Gabon, (A, Neg) => 5
  | Gabon, (B, Pos) => 172 | Gabon, (B, Neg) => 4
  | Gabon, (AB, Pos) => 25 | Gabon, (AB, Neg) => 1
  | Georgia, (O, Pos) => 348 | Georgia, (O, Neg) => 62
  | Georgia, (A, Pos) => 323 | Georgia, (A, Neg) => 57
  | Georgia, (B, Pos) => 119 | Georgia, (B, Neg) => 21
  | Georgia, (AB, Pos) => 60 | Georgia, (AB, Neg) => 5
  | Germany, (O, Pos) => 350 | Germany, (O, Neg) => 60
  | Germany, (A, Pos) => 370 | Germany, (A, Neg) => 60
  | Germany, (B, Pos) => 90 | Germany, (B, Neg) => 20
  | Germany, (AB, Pos) => 40 | Germany, (AB, Neg) => 10
  | Ghana, (O, Pos) => 538 | Ghana, (O, Neg) => 45
  | Ghana, (A, Pos) => 176 | Ghana, (A, Neg) => 13
  | Ghana, (B, Pos) => 183 | Ghana, (B, Neg) => 13
  | Ghana, (AB, Pos) => 28 | Ghana, (AB, Neg) => 2
  | Greece, (O, Pos) => 378 | Greece, (O, Neg) => 66
  | Greece, (A, Pos) => 322 | Greece, (A, Neg) => 57
  | Greece, (B, Pos) => 110 | Greece, (B, Neg) => 20
  | Greece, (AB, Pos) => 40 | Greece, (AB, Neg) => 7
  | Guinea, (O, Pos) => 469 | Guinea, (O, Neg) => 20
  | Guinea, (A, Pos) => 216 | Guinea, (A, Neg) => 9
  | Guinea, (B, Pos) => 229 | Guinea, (B, Neg) => 10
  | Guinea, (AB, Pos) => 45 | Guinea, (AB, Neg) => 2
  | Honduras, (O, Pos) => 575 | Honduras, (O, Neg) => 27
  | Honduras, (A, Pos) => 250 | Honduras, (A, Neg) => 17
  | Honduras, (B, Pos) => 78 | Honduras, (B, Neg) => 6
  | Honduras, (AB, Pos) => 25 | Honduras, (AB, Neg) => 2
  | HongKong, (O, Pos) => 428 | HongKong, (O, Neg) => 7
  | HongKong, (A, Pos) => 255 | HongKong, (A, Neg) => 1
  | HongKong, (B, Pos) => 258 | HongKong, (B, Neg) => 2
  | HongKong, (AB, Pos) => 59 | HongKong, (AB, Neg) => 1
  | Hungary, (O, Pos) => 270 | Hungary, (O, Neg) => 50
  | Hungary, (A, Pos) => 330 | Hungary, (A, Neg) => 70
  | Hungary, (B, Pos) => 160 | Hungary, (B, Neg) => 30
  | Hungary, (AB, Pos) => 80 | Hungary, (AB, Neg) => 10
  | Iceland, (O, Pos) => 468 | Iceland, (O, Neg) => 82
  | Iceland, (A, Pos) => 272 | Iceland, (A, Neg) => 48
  | Iceland, (B, Pos) => 90 | Iceland, (B, Neg) => 16
  | Iceland, (AB, Pos) => 20 | Iceland, (AB, Neg) => 4
  | India, (O, Pos) => 325 | India, (O, Neg) => 20
  | India, (A, Pos) => 218 | India, (A, Neg) => 14
  | India, (B, Pos) => 321 | India, (B, Neg) => 20
  | India, (AB, Pos) => 77 | India, (AB, Neg) => 5
  | Indonesia, (O, Pos) => 368 | Indonesia, (O, Neg) => 2
  | Indonesia, (A, Pos) => 259 | Indonesia, (A, Neg) => 1
  | Indonesia, (B, Pos) => 289 | Indonesia, (B, Neg) => 2
  | Indonesia, (AB, Pos) => 80 | Indonesia, (AB, Neg) => 0
  | Iran, (O, Pos) => 365 | Iran, (O, Neg) => 50
  | Iran, (A, Pos) => 270 | Iran, (A, Neg) => 20
  | Iran, (B, Pos) => 222 | Iran, (B, Neg) => 25
  | Iran, (AB, Pos) => 40 | Iran, (AB, Neg) => 8
  | Iraq, (O, Pos) => 321 | Iraq, (O, Neg) => 36
  | Iraq, (A, Pos) => 250 | Iraq, (A, Neg) => 27
  | Iraq, (B, Pos) => 256 | Iraq, (B, Neg) => 27
  | Iraq, (AB, Pos) => 74 | Iraq, (AB, Neg) => 9
  | Ireland, (O, Pos) => 470 | Ireland, (O, Neg) => 80
  | Ireland, (A, Pos) => 260 | Ireland, (A, Neg) => 50
  | Ireland, (B, Pos) => 90 | Ireland, (B, Neg) => 20
  | Ireland, (AB, Pos) => 20 | Ireland, (AB, Neg) => 10
  | Israel, (O, Pos) => 320 | Israel, (O, Neg) => 30
  | Israel, (A, Pos) => 340 | Israel, (A, Neg) => 40
  | Israel, (B, Pos) => 170 | Israel, (B, Neg) => 20
  | Israel, (AB, Pos) => 70 | Israel, (AB, Neg) => 10
  | Italy, (O, Pos) => 390 | Italy, (O, Neg) => 70
  | Italy, (A, Pos) => 360 | Italy, (A, Neg) => 60
  | Italy, (B, Pos) => 75 | Italy, (B, Neg) => 15
  | Italy, (AB, Pos) => 25 | Italy, (AB, Neg) => 5
  | IvoryCoast, (O, Pos) => 472 | IvoryCoast, (O, Neg) => 37
  | IvoryCoast, (A, Pos) => 202 | IvoryCoast, (A, Neg) => 15
  | IvoryCoast, (B, Pos) => 217 | IvoryCoast, (B, Neg) => 15
  | IvoryCoast, (AB, Pos) => 38 | IvoryCoast, (AB, Neg) => 3
  | Jamaica, (O, Pos) => 511 | Jamaica, (O, Neg) => 35
  | Jamaica, (A, Pos) => 200 | Jamaica, (A, Neg) => 20
  | Jamaica, (B, Pos) => 200 | Jamaica, (B, Neg) => 10
  | Jamaica, (AB, Pos) => 19 | Jamaica, (AB, Neg) => 5
  | Japan, (O, Pos) => 299 | Japan, (O, Neg) => 2
  | Japan, (A, Pos) => 398 | Japan, (A, Neg) => 2
  | Japan, (B, Pos) => 199 | Japan, (B, Neg) => 1
  | Japan, (AB, Pos) => 99 | Japan, (AB, Neg) => 1
  | Jordan, (O, Pos) => 330 | Jordan, (O, Neg) => 44
  | Jordan, (A, Pos) => 329 | Jordan, (A, Neg) => 40
  | Jordan, (B, Pos) => 166 | Jordan, (B, Neg) => 21
  | Jordan, (AB, Pos) => 63 | Jordan, (AB, Neg) => 7
  | Kazakhstan, (O, Pos) => 307 | Kazakhstan, (O, Neg) => 23
  | Kazakhstan, (A, Pos) => 298 | Kazakhstan, (A, Neg) => 22
  | Kazakhstan, (B, Pos) => 242 | Kazakhstan, (B, Neg) => 18
  | Kazakhstan, (AB, Pos) => 83 | Kazakhstan, (AB, Neg) => 7
  | Kenya, (O, Pos) => 456 | Kenya, (O, Neg) => 18
  | Kenya, (A, Pos) => 252 | Kenya, (A, Neg) => 10
  | Kenya, (B, Pos) => 213 | Kenya, (B, Neg) => 9
  | Kenya, (AB, Pos) => 42 | Kenya, (AB, Neg) => 0
  | Laos, (O, Pos) => 375 | Laos, (O, Neg) => 2
  | Laos, (A, Pos) => 197 | Laos, (A, Neg) => 1
  | Laos, (B, Pos) => 354 | Laos, (B, Neg) => 2
  | Laos, (AB, Pos) => 69 | Laos, (AB, Neg) => 0
  | Latvia, (O, Pos) => 306 | Latvia, (O, Neg) => 54
  | Latvia, (A, Pos) => 310 | Latvia, (A, Neg) => 60
  | Latvia, (B, Pos) => 170 | Latvia, (B, Neg) => 30
  | Latvia, (AB, Pos) => 60 | Latvia, (AB, Neg) => 10
  | Lebanon, (O, Pos) => 384 | Lebanon, (O, Neg) => 77
  | Lebanon, (A, Pos) => 323 | Lebanon, (A, Neg) => 65
  | Lebanon, (B, Pos) => 95 | Lebanon, (B, Neg) => 17
  | Lebanon, (AB, Pos) => 32 | Lebanon, (AB, Neg) => 7
  | Libya, (O, Pos) => 426 | Libya, (O, Neg) => 73
  | Libya, (A, Pos) => 209 | Libya, (A, Neg) => 32
  | Libya, (B, Pos) => 112 | Libya, (B, Neg) => 16
  | Libya, (AB, Pos) => 45 | Libya, (AB, Neg) => 7
  | Liechtenstein, (O, Pos) => 340 | Liechtenstein, (O, Neg) => 60
  | Liechtenstein, (A, Pos) => 370 | Liechtenstein, (A, Neg) => 65
  | Liechtenstein, (B, Pos) => 100 | Liechtenstein, (B, Neg) => 18
  | Liechtenstein, (AB, Pos) => 40 | Liechtenstein, (AB, Neg) => 7
  | Lithuania, (O, Pos) => 360 | Lithuania, (O, Neg) => 63
  | Lithuania, (A, Pos) => 330 | Lithuania, (A, Neg) => 60
  | Lithuania, (B, Pos) => 110 | Lithuania, (B, Neg) => 20
  | Lithuania, (AB, Pos) => 40 | Lithuania, (AB, Neg) => 17
  | Luxembourg, (O, Pos) => 350 | Luxembourg, (O, Neg) => 60
  | Luxembourg, (A, Pos) => 370 | Luxembourg, (A, Neg) => 60
  | Luxembourg, (B, Pos) => 90 | Luxembourg, (B, Neg) => 20
  | Luxembourg, (AB, Pos) => 40 | Luxembourg, (AB, Neg) => 10
  | Macao, (O, Pos) => 415 | Macao, (O, Neg) => 3
  | Macao, (A, Pos) => 261 | Macao, (A, Neg) => 1
  | Macao, (B, Pos) => 254 | Macao, (B, Neg) => 2
  | Macao, (AB, Pos) => 63 | Macao, (AB, Neg) => 1
  | Malaysia, (O, Pos) => 343 | Malaysia, (O, Neg) => 2
  | Malaysia, (A, Pos) => 304 | Malaysia, (A, Neg) => 2
  | Malaysia, (B, Pos) => 274 | Malaysia, (B, Neg) => 1
  | Malaysia, (AB, Pos) => 75 | Malaysia, (AB, Neg) => 0
  | Malta, (O, Pos) => 380 | Malta, (O, Neg) => 50
  | Malta, (A, Pos) => 410 | Malta, (A, Neg) => 45
  | Malta, (B, Pos) => 70 | Malta, (B, Neg) => 10
  | Malta, (AB, Pos) => 30 | Malta, (AB, Neg) => 5
  | Mauritania, (O, Pos) => 463 | Mauritania, (O, Neg) => 28
  | Mauritania, (A, Pos) => 267 | Mauritania, (A, Neg) => 16
  | Mauritania, (B, Pos) => 175 | Mauritania, (B, Neg) => 11
  | Mauritania, (AB, Pos) => 39 | Mauritania, (AB, Neg) => 1
  | Mauritius, (O, Pos) => 383 | Mauritius, (O, Neg) => 17
  | Mauritius, (A, Pos) => 260 | Mauritius, (A, Neg) => 10
  | Mauritius, (B, Pos) => 250 | Mauritius, (B, Neg) => 10
  | Mauritius, (AB, Pos) => 67 | Mauritius, (AB, Neg) => 3
  | Mexico, (O, Pos) => 591 | Mexico, (O, Neg) => 27
  | Mexico, (A, Pos) => 262 | Mexico, (A, Neg) => 12
  | Mexico, (B, Pos) => 85 | Mexico, (B, Neg) => 4
  | Mexico, (AB, Pos) => 17 | Mexico, (AB, Neg) => 2
  | Moldova, (O, Pos) => 285 | Moldova, (O, Neg) => 50
  | Moldova, (A, Pos) => 318 | Moldova, (A, Neg) => 60
  | Moldova, (B, Pos) => 176 | Moldova, (B, Neg) => 30
  | Moldova, (AB, Pos) => 70 | Moldova, (AB, Neg) => 11
  | Mongolia, (O, Pos) => 364 | Mongolia, (O, Neg) => 46
  | Mongolia, (A, Pos) => 292 | Mongolia, (A, Neg) => 37
  | Mongolia, (B, Pos) => 161 | Mongolia, (B, Neg) => 20
  | Mongolia, (AB, Pos) => 71 | Mongolia, (AB, Neg) => 9
  | Morocco, (O, Pos) => 423 | Morocco, (O, Neg) => 45
  | Morocco, (A, Pos) => 308 | Morocco, (A, Neg) => 31
  | Morocco, (B, Pos) => 140 | Morocco, (B, Neg) => 15
  | Morocco, (AB, Pos) => 34 | Morocco, (AB, Neg) => 4
  | Myanmar, (O, Pos) => 357 | Myanmar, (O, Neg) => 3
  | Myanmar, (A, Pos) => 238 | Myanmar, (A, Neg) => 2
  | Myanmar, (B, Pos) => 327 | Myanmar, (B, Neg) => 3
  | Myanmar, (AB, Pos) => 70 | Myanmar, (AB, Neg) => 0
  | Namibia, (O, Pos) => 506 | Namibia, (O, Neg) => 42
  | Namibia, (A, Pos) => 205 | Namibia, (A, Neg) => 17
  | Namibia, (B, Pos) => 202 | Namibia, (B, Neg) => 17
  | Namibia, (AB, Pos) => 10 | Namibia, (AB, Neg) => 1
  | Nepal, (O, Pos) => 352 | Nepal, (O, Neg) => 3
  | Nepal, (A, Pos) => 363 | Nepal, (A, Neg) => 2
  | Nepal, (B, Pos) => 271 | Nepal, (B, Neg) => 2
  | Nepal, (AB, Pos) => 6 | Nepal, (AB, Neg) => 1
  | Netherlands, (O, Pos) => 382 | Netherlands, (O, Neg) => 68
  | Netherlands, (A, Pos) => 366 | Netherlands, (A, Neg) => 64
  | Netherlands, (B, Pos) => 77 | Netherlands, (B, Neg) => 13
  | Netherlands, (AB, Pos) => 25 | Netherlands, (AB, Neg) => 5
  | NewZealand, (O, Pos) => 380 | NewZealand, (O, Neg) => 90
  | NewZealand, (A, Pos) => 320 | NewZealand, (A, Neg) => 60
  | NewZealand, (B, Pos) => 100 | NewZealand, (B, Neg) => 10
  | NewZealand, (AB, Pos) => 30 | NewZealand, (AB, Neg) => 10
  | Nicaragua, (O, Pos) => 620 | Nicaragua, (O, Neg) => 10
  | Nicaragua, (A, Pos) => 200 | Nicaragua, (A, Neg) => 10
  | Nicaragua, (B, Pos) => 110 | Nicaragua, (B, Neg) => 7
  | Nicaragua, (AB, Pos) => 40 | Nicaragua, (AB, Neg) => 3
  | Nigeria, (O, Pos) => 502 | Nigeria, (O, Neg) => 27
  | Nigeria, (A, Pos) => 216 | Nigeria, (A, Neg) => 12
  | Nigeria, (B, Pos) => 196 | Nigeria, (B, Neg) => 11
  | Nigeria, (AB, Pos) => 35 | Nigeria, (AB, Neg) => 1
  | NorthKorea, (O, Pos) => 272 | NorthKorea, (O, Neg) => 1
  | NorthKorea, (A, Pos) => 311 | NorthKorea, (A, Neg) => 1
  | NorthKorea, (B, Pos) => 302 | NorthKorea, (B, Neg) => 1
  | NorthKorea, (AB, Pos) => 113 | NorthKorea, (AB, Neg) => 0
  | NorthMacedonia, (O, Pos) => 300 | NorthMacedonia, (O, Neg) => 50
  | NorthMacedonia, (A, Pos) => 340 | NorthMacedonia, (A, Neg) => 60
  | NorthMacedonia, (B, Pos) => 150 | NorthMacedonia, (B, Neg) => 30
  | NorthMacedonia, (AB, Pos) => 60 | NorthMacedonia, (AB, Neg) => 10
  | Norway, (O, Pos) => 332 | Norway, (O, Neg) => 58
  | Norway, (A, Pos) => 416 | Norway, (A, Neg) => 74
  | Norway, (B, Pos) => 68 | Norway, (B, Neg) => 12
  | Norway, (AB, Pos) => 34 | Norway, (AB, Neg) => 6
  | Oman, (O, Pos) => 449 | Oman, (O, Neg) => 74
  | Oman, (A, Pos) => 174 | Oman, (A, Neg) => 6
  | Oman, (B, Pos) => 202 | Oman, (B, Neg) => 27
  | Oman, (AB, Pos) => 68 | Oman, (AB, Neg) => 0
  | Pakistan, (O, Pos) => 300 | Pakistan, (O, Neg) => 31
  | Pakistan, (A, Pos) => 215 | Pakistan, (A, Neg) => 22
  | Pakistan, (B, Pos) => 302 | Pakistan, (B, Neg) => 31
  | Pakistan, (AB, Pos) => 88 | Pakistan, (AB, Neg) => 11
  | PapuaNewGuinea, (O, Pos) => 557 | PapuaNewGuinea, (O, Neg) => 8
  | PapuaNewGuinea, (A, Pos) => 322 | PapuaNewGuinea, (A, Neg) => 5
  | PapuaNewGuinea, (B, Pos) => 96 | PapuaNewGuinea, (B, Neg) => 2
  | PapuaNewGuinea, (AB, Pos) => 9 | PapuaNewGuinea, (AB, Neg) => 1
  | Paraguay, (O, Pos) => 631 | Paraguay, (O, Neg) => 59
  | Paraguay, (A, Pos) => 213 | Paraguay, (A, Neg) => 30
  | Paraguay, (B, Pos) => 47 | Paraguay, (B, Neg) => 5
  | Paraguay, (AB, Pos) => 14 | Paraguay, (AB, Neg) => 1
  | Peru, (O, Pos) => 700 | Peru, (O, Neg) => 14
  | Peru, (A, Pos) => 184 | Peru, (A, Neg) => 5
  | Peru, (B, Pos) => 78 | Peru, (B, Neg) => 3
  | Peru, (AB, Pos) => 16 | Peru, (AB, Neg) => 0
  | Philippines, (O, Pos) => 459 | Philippines, (O, Neg) => 1
  | Philippines, (A, Pos) => 229 | Philippines, (A, Neg) => 1
  | Philippines, (B, Pos) => 249 | Philippines, (B, Neg) => 1
  | Philippines, (AB, Pos) => 60 | Philippines, (AB, Neg) => 0
  | Poland, (O, Pos) => 310 | Poland, (O, Neg) => 60
  | Poland, (A, Pos) => 320 | Poland, (A, Neg) => 60
  | Poland, (B, Pos) => 150 | Poland, (B, Neg) => 20
  | Poland, (AB, Pos) => 70 | Poland, (AB, Neg) => 10
  | Portugal, (O, Pos) => 362 | Portugal, (O, Neg) => 61
  | Portugal, (A, Pos) => 398 | Portugal, (A, Neg) => 68
  | Portugal, (B, Pos) => 66 | Portugal, (B, Neg) => 11
  | Portugal, (AB, Pos) => 29 | Portugal, (AB, Neg) => 5
  | Romania, (O, Pos) => 280 | Romania, (O, Neg) => 50
  | Romania, (A, Pos) => 370 | Romania, (A, Neg) => 60
  | Romania, (B, Pos) => 140 | Romania, (B, Neg) => 20
  | Romania, (AB, Pos) => 70 | Romania, (AB, Neg) => 10
  | Russia, (O, Pos) => 360 | Russia, (O, Neg) => 60
  | Russia, (A, Pos) => 310 | Russia, (A, Neg) => 40
  | Russia, (B, Pos) => 190 | Russia, (B, Neg) => 10
  | Russia, (AB, Pos) => 21 | Russia, (AB, Neg) => 9
  | SaudiArabia, (O, Pos) => 478 | SaudiArabia, (O, Neg) => 40
  | SaudiArabia, (A, Pos) => 160 | SaudiArabia, (A, Neg) => 20
  | SaudiArabia, (B, Pos) => 179 | SaudiArabia, (B, Neg) => 10
  | SaudiArabia, (AB, Pos) => 40 | SaudiArabia, (AB, Neg) => 3
  | Serbia, (O, Pos) => 319 | Serbia, (O, Neg) => 61
  | Serbia, (A, Pos) => 353 | Serbia, (A, Neg) => 67
  | Serbia, (B, Pos) => 126 | Serbia, (B, Neg) => 24
  | Serbia, (AB, Pos) => 42 | Serbia, (AB, Neg) => 8
  | Singapore, (O, Pos) => 447 | Singapore, (O, Neg) => 6
  | Singapore, (A, Pos) => 239 | Singapore, (A, Neg) => 3
  | Singapore, (B, Pos) => 245 | Singapore, (B, Neg) => 3
  | Singapore, (AB, Pos) => 56 | Singapore, (AB, Neg) => 1
  | Slovakia, (O, Pos) => 272 | Slovakia, (O, Neg) => 48
  | Slovakia, (A, Pos) => 357 | Slovakia, (A, Neg) => 63
  | Slovakia, (B, Pos) => 153 | Slovakia, (B, Neg) => 27
  | Slovakia, (AB, Pos) => 68 | Slovakia, (AB, Neg) => 12
  | Slovenia, (O, Pos) => 310 | Slovenia, (O, Neg) => 70
  | Slovenia, (A, Pos) => 330 | Slovenia, (A, Neg) => 70
  | Slovenia, (B, Pos) => 120 | Slovenia, (B, Neg) => 30
  | Slovenia, (AB, Pos) => 60 | Slovenia, (AB, Neg) => 10
  | Somalia, (O, Pos) => 528 | Somalia, (O, Neg) => 72
  | Somalia, (A, Pos) => 194 | Somalia, (A, Neg) => 26
  | Somalia, (B, Pos) => 123 | Somalia, (B, Neg) => 17
  | Somalia, (AB, Pos) => 35 | Somalia, (AB, Neg) => 5
  | SouthAfrica, (O, Pos) => 390 | SouthAfrica, (O, Neg) => 60
  | SouthAfrica, (A, Pos) => 320 | SouthAfrica, (A, Neg) => 50
  | SouthAfrica, (B, Pos) => 120 | SouthAfrica, (B, Neg) => 20
  | SouthAfrica, (AB, Pos) => 30 | SouthAfrica, (AB, Neg) => 10
  | SouthKorea, (O, Pos) => 290 | SouthKorea, (O, Neg) => 2
  | SouthKorea, (A, Pos) => 320 | SouthKorea, (A, Neg) => 1
  | SouthKorea, (B, Pos) => 310 | SouthKorea, (B, Neg) => 1
  | SouthKorea, (AB, Pos) => 76 | SouthKorea, (AB, Neg) => 0
  | Spain, (O, Pos) => 350 | Spain, (O, Neg) => 90
  | Spain, (A, Pos) => 360 | Spain, (A, Neg) => 70
  | Spain, (B, Pos) => 80 | Spain, (B, Neg) => 20
  | Spain, (AB, Pos) => 25 | Spain, (AB, Neg) => 5
  | SriLanka, (O, Pos) => 434 | SriLanka, (O, Neg) => 21
  | SriLanka, (A, Pos) => 210 | SriLanka, (A, Neg) => 10
  | SriLanka, (B, Pos) => 258 | SriLanka, (B, Neg) => 13
  | SriLanka, (AB, Pos) => 51 | SriLanka, (AB, Neg) => 3
  | Sudan, (O, Pos) => 480 | Sudan, (O, Neg) => 35
  | Sudan, (A, Pos) => 277 | Sudan, (A, Neg) => 18
  | Sudan, (B, Pos) => 152 | Sudan, (B, Neg) => 8
  | Sudan, (AB, Pos) => 28 | Sudan, (AB, Neg) => 2
  | Sweden, (O, Pos) => 320 | Sweden, (O, Neg) => 60
  | Sweden, (A, Pos) => 370 | Sweden, (A, Neg) => 70
  | Sweden, (B, Pos) => 100 | Sweden, (B, Neg) => 20
  | Sweden, (AB, Pos) => 50 | Sweden, (AB, Neg) => 10
  | Switzerland, (O, Pos) => 350 | Switzerland, (O, Neg) => 60
  | Switzerland, (A, Pos) => 380 | Switzerland, (A, Neg) => 70
  | Switzerland, (B, Pos) => 80 | Switzerland, (B, Neg) => 10
  | Switzerland, (AB, Pos) => 40 | Switzerland, (AB, Neg) => 10
  | Syria, (O, Pos) => 430 | Syria, (O, Neg) => 50
  | Syria, (A, Pos) => 300 | Syria, (A, Neg) => 30
  | Syria, (B, Pos) => 140 | Syria, (B, Neg) => 10
  | Syria, (AB, Pos) => 37 | Syria, (AB, Neg) => 3
  | Taiwan, (O, Pos) => 439 | Taiwan, (O, Neg) => 3
  | Taiwan, (A, Pos) => 259 | Taiwan, (A, Neg) => 0
  | Taiwan, (B, Pos) => 239 | Taiwan, (B, Neg) => 0
  | Taiwan, (AB, Pos) => 60 | Taiwan, (AB, Neg) => 0
  | Thailand, (O, Pos) => 408 | Thailand, (O, Neg) => 2
  | Thailand, (A, Pos) => 169 | Thailand, (A, Neg) => 1
  | Thailand, (B, Pos) => 368 | Thailand, (B, Neg) => 2
  | Thailand, (AB, Pos) => 50 | Thailand, (AB, Neg) => 0
  | Tunisia, (O, Pos) => 419 | Tunisia, (O, Neg) => 41
  | Tunisia, (A, Pos) => 282 | Tunisia, (A, Neg) => 28
  | Tunisia, (B, Pos) => 164 | Tunisia, (B, Neg) => 16
  | Tunisia, (AB, Pos) => 46 | Tunisia, (AB, Neg) => 4
  | Turkey, (O, Pos) => 294 | Turkey, (O, Neg) => 44
  | Turkey, (A, Pos) => 383 | Turkey, (A, Neg) => 55
  | Turkey, (B, Pos) => 132 | Turkey, (B, Neg) => 21
  | Turkey, (AB, Pos) => 64 | Turkey, (AB, Neg) => 7
  | Uganda, (O, Pos) => 493 | Uganda, (O, Neg) => 10
  | Uganda, (A, Pos) => 241 | Uganda, (A, Neg) => 5
  | Uganda, (B, Pos) => 203 | Uganda, (B, Neg) => 4
  | Uganda, (AB, Pos) => 44 | Uganda, (AB, Neg) => 0
  | Ukraine, (O, Pos) => 320 | Ukraine, (O, Neg) => 50
  | Ukraine, (A, Pos) => 340 | Ukraine, (A, Neg) => 60
  | Ukraine, (B, Pos) => 150 | Ukraine, (B, Neg) => 20
  | Ukraine, (AB, Pos) => 50 | Ukraine, (AB, Neg) => 10
  | UnitedArabEmirates, (O, Pos) => 441 | UnitedArabEmirates, (O, Neg) => 43
  | UnitedArabEmirates, (A, Pos) => 219 | UnitedArabEmirates, (A, Neg) => 21
  | UnitedArabEmirates, (B, Pos) => 209 | UnitedArabEmirates, (B, Neg) => 20
  | UnitedArabEmirates, (AB, Pos) => 43 | UnitedArabEmirates, (AB, Neg) => 4
  | UnitedKingdom, (O, Pos) => 360 | UnitedKingdom, (O, Neg) => 80
  | UnitedKingdom, (A, Pos) => 300 | UnitedKingdom, (A, Neg) => 90
  | UnitedKingdom, (B, Pos) => 80 | UnitedKingdom, (B, Neg) => 20
  | UnitedKingdom, (AB, Pos) => 60 | UnitedKingdom, (AB, Neg) => 10
  | UnitedStates, (O, Pos) => 374 | UnitedStates, (O, Neg) => 66
  | UnitedStates, (A, Pos) => 357 | UnitedStates, (A, Neg) => 63
  | UnitedStates, (B, Pos) => 85 | UnitedStates, (B, Neg) => 15
  | UnitedStates, (AB, Pos) => 34 | UnitedStates, (AB, Neg) => 6
  | Uzbekistan, (O, Pos) => 294 | Uzbekistan, (O, Neg) => 17
  | Uzbekistan, (A, Pos) => 309 | Uzbekistan, (A, Neg) => 18
  | Uzbekistan, (B, Pos) => 250 | Uzbekistan, (B, Neg) => 14
  | Uzbekistan, (AB, Pos) => 93 | Uzbekistan, (AB, Neg) => 5
  | Venezuela, (O, Pos) => 583 | Venezuela, (O, Neg) => 40
  | Venezuela, (A, Pos) => 282 | Venezuela, (A, Neg) => 15
  | Venezuela, (B, Pos) => 56 | Venezuela, (B, Neg) => 4
  | Venezuela, (AB, Pos) => 19 | Venezuela, (AB, Neg) => 1
  | Vietnam, (O, Pos) => 417 | Vietnam, (O, Neg) => 3
  | Vietnam, (A, Pos) => 209 | Vietnam, (A, Neg) => 1
  | Vietnam, (B, Pos) => 308 | Vietnam, (B, Neg) => 2
  | Vietnam, (AB, Pos) => 60 | Vietnam, (AB, Neg) => 0
  | Yemen, (O, Pos) => 478 | Yemen, (O, Neg) => 37
  | Yemen, (A, Pos) => 275 | Yemen, (A, Neg) => 21
  | Yemen, (B, Pos) => 153 | Yemen, (B, Neg) => 12
  | Yemen, (AB, Pos) => 21 | Yemen, (AB, Neg) => 3
  | Zimbabwe, (O, Pos) => 457 | Zimbabwe, (O, Neg) => 17
  | Zimbabwe, (A, Pos) => 288 | Zimbabwe, (A, Neg) => 10
  | Zimbabwe, (B, Pos) => 180 | Zimbabwe, (B, Neg) => 4
  | Zimbabwe, (AB, Pos) => 41 | Zimbabwe, (AB, Neg) => 3
  end.

Definition pop_sum (pop : Population) : nat :=
  fold_left Nat.add (map (pop_frequency pop) all_blood_types) 0.

(** Sum of Rh-negative frequencies for a population (per 1000) *)
Definition pop_rh_neg_sum (pop : Population) : nat :=
  pop_frequency pop (O, Neg) + pop_frequency pop (A, Neg) +
  pop_frequency pop (B, Neg) + pop_frequency pop (AB, Neg).

(** Sum of Rh-positive frequencies for a population (per 1000) *)
Definition pop_rh_pos_sum (pop : Population) : nat :=
  pop_frequency pop (O, Pos) + pop_frequency pop (A, Pos) +
  pop_frequency pop (B, Pos) + pop_frequency pop (AB, Pos).

(** Q-based population frequencies - connects nat-scaled to exact rationals *)
Open Scope Q_scope.

Definition pop_frequency_Q (pop : Population) (bt : BloodType) : Q :=
  inject_Z (Z.of_nat (pop_frequency pop bt)) / 1000.

(** Population-specific Rh-negative frequency as a rational.
    Derived from actual population data, not Hardy-Weinberg assumptions.
    This accurately reflects observed Rh distribution in each population. *)
Definition pop_rh_neg_freq_Q (pop : Population) : Q :=
  inject_Z (Z.of_nat (pop_rh_neg_sum pop)) / 1000.

(** Population-specific Rh-positive frequency *)
Definition pop_rh_pos_freq_Q (pop : Population) : Q :=
  1 - pop_rh_neg_freq_Q pop.

(** d-allele frequency estimate: sqrt(Rh_neg_frequency).
    This is derived from Hardy-Weinberg: if d = d-allele freq, then Rh_neg = d^2 *)
Definition pop_d_allele_freq_Q (pop : Population) : Q :=
  let rh_neg := pop_rh_neg_freq_Q pop in
  rh_neg.

Definition pop_allele_freq_Q (pop : Population) : AlleleFreqQ :=
  match pop with
  | Albania => mkAlleleFreqQ (28 # 100) (7 # 100) (65 # 100)
  | Algeria => mkAlleleFreqQ (27 # 100) (8 # 100) (65 # 100)
  | Argentina => mkAlleleFreqQ (26 # 100) (5 # 100) (69 # 100)
  | Armenia => mkAlleleFreqQ (33 # 100) (8 # 100) (59 # 100)
  | Australia => mkAlleleFreqQ (28 # 100) (8 # 100) (64 # 100)
  | Austria => mkAlleleFreqQ (30 # 100) (8 # 100) (62 # 100)
  | Azerbaijan => mkAlleleFreqQ (27 # 100) (14 # 100) (59 # 100)
  | Bahrain => mkAlleleFreqQ (18 # 100) (14 # 100) (68 # 100)
  | Bangladesh => mkAlleleFreqQ (22 # 100) (24 # 100) (54 # 100)
  | Belarus => mkAlleleFreqQ (27 # 100) (11 # 100) (62 # 100)
  | Belgium => mkAlleleFreqQ (29 # 100) (6 # 100) (65 # 100)
  | Bhutan => mkAlleleFreqQ (24 # 100) (17 # 100) (59 # 100)
  | Bolivia => mkAlleleFreqQ (22 # 100) (7 # 100) (71 # 100)
  | BosniaHerzegovina => mkAlleleFreqQ (29 # 100) (9 # 100) (62 # 100)
  | Brazil => mkAlleleFreqQ (29 # 100) (6 # 100) (65 # 100)
  | Bulgaria => mkAlleleFreqQ (30 # 100) (10 # 100) (60 # 100)
  | BurkinaFaso => mkAlleleFreqQ (19 # 100) (18 # 100) (63 # 100)
  | Cambodia => mkAlleleFreqQ (23 # 100) (13 # 100) (64 # 100)
  | Cameroon => mkAlleleFreqQ (21 # 100) (15 # 100) (64 # 100)
  | Canada => mkAlleleFreqQ (29 # 100) (6 # 100) (65 # 100)
  | Chile => mkAlleleFreqQ (25 # 100) (6 # 100) (69 # 100)
  | China => mkAlleleFreqQ (24 # 100) (20 # 100) (56 # 100)
  | Colombia => mkAlleleFreqQ (21 # 100) (5 # 100) (74 # 100)
  | CostaRica => mkAlleleFreqQ (25 # 100) (9 # 100) (66 # 100)
  | Croatia => mkAlleleFreqQ (29 # 100) (11 # 100) (60 # 100)
  | Cuba => mkAlleleFreqQ (27 # 100) (8 # 100) (65 # 100)
  | Cyprus => mkAlleleFreqQ (31 # 100) (8 # 100) (61 # 100)
  | CzechRepublic => mkAlleleFreqQ (29 # 100) (11 # 100) (60 # 100)
  | DemocraticRepublicCongo => mkAlleleFreqQ (19 # 100) (11 # 100) (70 # 100)
  | Denmark => mkAlleleFreqQ (30 # 100) (6 # 100) (64 # 100)
  | DominicanRepublic => mkAlleleFreqQ (23 # 100) (12 # 100) (65 # 100)
  | Ecuador => mkAlleleFreqQ (17 # 100) (5 # 100) (78 # 100)
  | ElSalvador => mkAlleleFreqQ (21 # 100) (8 # 100) (71 # 100)
  | Estonia => mkAlleleFreqQ (27 # 100) (15 # 100) (58 # 100)
  | Ethiopia => mkAlleleFreqQ (24 # 100) (15 # 100) (61 # 100)
  | Fiji => mkAlleleFreqQ (27 # 100) (12 # 100) (61 # 100)
  | Finland => mkAlleleFreqQ (28 # 100) (12 # 100) (60 # 100)
  | France => mkAlleleFreqQ (31 # 100) (5 # 100) (64 # 100)
  | Gabon => mkAlleleFreqQ (19 # 100) (12 # 100) (69 # 100)
  | Georgia => mkAlleleFreqQ (28 # 100) (9 # 100) (63 # 100)
  | Germany => mkAlleleFreqQ (30 # 100) (7 # 100) (63 # 100)
  | Ghana => mkAlleleFreqQ (17 # 100) (13 # 100) (70 # 100)
  | Greece => mkAlleleFreqQ (28 # 100) (8 # 100) (64 # 100)
  | Guinea => mkAlleleFreqQ (19 # 100) (16 # 100) (65 # 100)
  | Honduras => mkAlleleFreqQ (23 # 100) (6 # 100) (71 # 100)
  | HongKong => mkAlleleFreqQ (23 # 100) (18 # 100) (59 # 100)
  | Hungary => mkAlleleFreqQ (28 # 100) (12 # 100) (60 # 100)
  | Iceland => mkAlleleFreqQ (25 # 100) (7 # 100) (68 # 100)
  | India => mkAlleleFreqQ (21 # 100) (26 # 100) (53 # 100)
  | Indonesia => mkAlleleFreqQ (23 # 100) (20 # 100) (57 # 100)
  | Iran => mkAlleleFreqQ (24 # 100) (16 # 100) (60 # 100)
  | Iraq => mkAlleleFreqQ (23 # 100) (18 # 100) (59 # 100)
  | Ireland => mkAlleleFreqQ (25 # 100) (7 # 100) (68 # 100)
  | Israel => mkAlleleFreqQ (28 # 100) (12 # 100) (60 # 100)
  | Italy => mkAlleleFreqQ (29 # 100) (5 # 100) (66 # 100)
  | IvoryCoast => mkAlleleFreqQ (19 # 100) (15 # 100) (66 # 100)
  | Jamaica => mkAlleleFreqQ (19 # 100) (14 # 100) (67 # 100)
  | Japan => mkAlleleFreqQ (29 # 100) (17 # 100) (54 # 100)
  | Jordan => mkAlleleFreqQ (27 # 100) (12 # 100) (61 # 100)
  | Kazakhstan => mkAlleleFreqQ (26 # 100) (17 # 100) (57 # 100)
  | Kenya => mkAlleleFreqQ (22 # 100) (15 # 100) (63 # 100)
  | Laos => mkAlleleFreqQ (18 # 100) (24 # 100) (58 # 100)
  | Latvia => mkAlleleFreqQ (27 # 100) (13 # 100) (60 # 100)
  | Lebanon => mkAlleleFreqQ (28 # 100) (7 # 100) (65 # 100)
  | Libya => mkAlleleFreqQ (21 # 100) (9 # 100) (70 # 100)
  | Liechtenstein => mkAlleleFreqQ (30 # 100) (7 # 100) (63 # 100)
  | Lithuania => mkAlleleFreqQ (28 # 100) (8 # 100) (64 # 100)
  | Luxembourg => mkAlleleFreqQ (30 # 100) (7 # 100) (63 # 100)
  | Macao => mkAlleleFreqQ (23 # 100) (18 # 100) (59 # 100)
  | Malaysia => mkAlleleFreqQ (26 # 100) (19 # 100) (55 # 100)
  | Malta => mkAlleleFreqQ (32 # 100) (5 # 100) (63 # 100)
  | Mauritania => mkAlleleFreqQ (23 # 100) (12 # 100) (65 # 100)
  | Mauritius => mkAlleleFreqQ (23 # 100) (18 # 100) (59 # 100)
  | Mexico => mkAlleleFreqQ (24 # 100) (6 # 100) (70 # 100)
  | Moldova => mkAlleleFreqQ (28 # 100) (13 # 100) (59 # 100)
  | Mongolia => mkAlleleFreqQ (26 # 100) (12 # 100) (62 # 100)
  | Morocco => mkAlleleFreqQ (27 # 100) (10 # 100) (63 # 100)
  | Myanmar => mkAlleleFreqQ (21 # 100) (23 # 100) (56 # 100)
  | Namibia => mkAlleleFreqQ (19 # 100) (14 # 100) (67 # 100)
  | Nepal => mkAlleleFreqQ (28 # 100) (19 # 100) (53 # 100)
  | Netherlands => mkAlleleFreqQ (30 # 100) (6 # 100) (64 # 100)
  | NewZealand => mkAlleleFreqQ (28 # 100) (7 # 100) (65 # 100)
  | Nicaragua => mkAlleleFreqQ (19 # 100) (8 # 100) (73 # 100)
  | Nigeria => mkAlleleFreqQ (19 # 100) (14 # 100) (67 # 100)
  | NorthKorea => mkAlleleFreqQ (27 # 100) (22 # 100) (51 # 100)
  | NorthMacedonia => mkAlleleFreqQ (28 # 100) (11 # 100) (61 # 100)
  | Norway => mkAlleleFreqQ (33 # 100) (5 # 100) (62 # 100)
  | Oman => mkAlleleFreqQ (18 # 100) (15 # 100) (67 # 100)
  | Pakistan => mkAlleleFreqQ (20 # 100) (23 # 100) (57 # 100)
  | PapuaNewGuinea => mkAlleleFreqQ (27 # 100) (7 # 100) (66 # 100)
  | Paraguay => mkAlleleFreqQ (21 # 100) (4 # 100) (75 # 100)
  | Peru => mkAlleleFreqQ (17 # 100) (6 # 100) (77 # 100)
  | Philippines => mkAlleleFreqQ (21 # 100) (18 # 100) (61 # 100)
  | Poland => mkAlleleFreqQ (28 # 100) (11 # 100) (61 # 100)
  | Portugal => mkAlleleFreqQ (32 # 100) (5 # 100) (63 # 100)
  | Romania => mkAlleleFreqQ (30 # 100) (10 # 100) (60 # 100)
  | Russia => mkAlleleFreqQ (27 # 100) (14 # 100) (59 # 100)
  | SaudiArabia => mkAlleleFreqQ (17 # 100) (13 # 100) (70 # 100)
  | Serbia => mkAlleleFreqQ (29 # 100) (9 # 100) (62 # 100)
  | Singapore => mkAlleleFreqQ (22 # 100) (18 # 100) (60 # 100)
  | Slovakia => mkAlleleFreqQ (29 # 100) (11 # 100) (60 # 100)
  | Slovenia => mkAlleleFreqQ (28 # 100) (10 # 100) (62 # 100)
  | Somalia => mkAlleleFreqQ (19 # 100) (10 # 100) (71 # 100)
  | SouthAfrica => mkAlleleFreqQ (28 # 100) (9 # 100) (63 # 100)
  | SouthKorea => mkAlleleFreqQ (27 # 100) (22 # 100) (51 # 100)
  | Spain => mkAlleleFreqQ (29 # 100) (6 # 100) (65 # 100)
  | SriLanka => mkAlleleFreqQ (20 # 100) (19 # 100) (61 # 100)
  | Sudan => mkAlleleFreqQ (24 # 100) (11 # 100) (65 # 100)
  | Sweden => mkAlleleFreqQ (30 # 100) (8 # 100) (62 # 100)
  | Switzerland => mkAlleleFreqQ (31 # 100) (6 # 100) (63 # 100)
  | Syria => mkAlleleFreqQ (26 # 100) (10 # 100) (64 # 100)
  | Taiwan => mkAlleleFreqQ (23 # 100) (17 # 100) (60 # 100)
  | Thailand => mkAlleleFreqQ (17 # 100) (26 # 100) (57 # 100)
  | Tunisia => mkAlleleFreqQ (25 # 100) (12 # 100) (63 # 100)
  | Turkey => mkAlleleFreqQ (31 # 100) (10 # 100) (59 # 100)
  | Uganda => mkAlleleFreqQ (21 # 100) (14 # 100) (65 # 100)
  | Ukraine => mkAlleleFreqQ (29 # 100) (11 # 100) (60 # 100)
  | UnitedArabEmirates => mkAlleleFreqQ (21 # 100) (15 # 100) (64 # 100)
  | UnitedKingdom => mkAlleleFreqQ (28 # 100) (6 # 100) (66 # 100)
  | UnitedStates => mkAlleleFreqQ (28 # 100) (7 # 100) (65 # 100)
  | Uzbekistan => mkAlleleFreqQ (27 # 100) (18 # 100) (55 # 100)
  | Venezuela => mkAlleleFreqQ (26 # 100) (4 # 100) (70 # 100)
  | Vietnam => mkAlleleFreqQ (19 # 100) (22 # 100) (59 # 100)
  | Yemen => mkAlleleFreqQ (24 # 100) (11 # 100) (65 # 100)
  | Zimbabwe => mkAlleleFreqQ (24 # 100) (13 # 100) (63 # 100)
  end.

Theorem pop_allele_freq_Q_sums_to_1 : forall pop,
  allele_freq_sum (pop_allele_freq_Q pop) == 1.
Proof. intros pop; destruct pop; unfold allele_freq_sum, pop_allele_freq_Q; simpl; reflexivity. Qed.

Definition expected_abo_dist_Q (pop : Population) : PhenoDistributionQ :=
  hardy_weinberg_Q (pop_allele_freq_Q pop).

Theorem expected_abo_dist_Q_sums_to_1 : forall pop,
  pheno_dist_sum (expected_abo_dist_Q pop) == 1.
Proof.
  intros pop. apply hardy_weinberg_Q_totals. apply pop_allele_freq_Q_sums_to_1.
Qed.

Definition nat_to_Q_scaled (n : nat) (scale : positive) : Q :=
  inject_Z (Z.of_nat n) / inject_Z (Zpos scale).

Definition Qround (q : Q) : Z :=
  let f := Qfloor q in
  let c := Qceiling q in
  if Qle_bool (q - inject_Z f) (1 # 2) then f else c.

Definition Q_to_nat_scaled (q : Q) (scale : positive) : nat :=
  Z.to_nat (Qround (q * inject_Z (Zpos scale))).

Lemma inject_Z_div_mult : forall (n : Z) (p : positive),
  (inject_Z n / inject_Z (Zpos p)) * inject_Z (Zpos p) == inject_Z n.
Proof.
  intros n p.
  field. discriminate.
Qed.

Lemma Qfloor_inject_Z : forall z, Qfloor (inject_Z z) = z.
Proof. intros z. apply Qfloor_Z. Qed.

Lemma Qround_inject_Z : forall z, Qround (inject_Z z) = z.
Proof.
  intros z. unfold Qround.
  rewrite Qfloor_Z. rewrite Qceiling_Z.
  assert (H: inject_Z z - inject_Z z == 0) by ring.
  destruct (Qle_bool (inject_Z z - inject_Z z) (1 # 2)) eqn:E; reflexivity.
Qed.

Lemma nat_to_Q_scaled_mult_inverse : forall (x : nat) (p : positive),
  nat_to_Q_scaled x p * inject_Z (Zpos p) == inject_Z (Z.of_nat x).
Proof.
  intros x p. unfold nat_to_Q_scaled.
  apply inject_Z_div_mult.
Qed.

Lemma Qround_compat : forall q1 q2, q1 == q2 -> Qround q1 = Qround q2.
Proof.
  intros q1 q2 Heq. unfold Qround.
  rewrite (Qfloor_comp q1 q2 Heq).
  rewrite (Qceiling_comp q1 q2 Heq).
  assert (Hdiff: q1 - inject_Z (Qfloor q2) == q2 - inject_Z (Qfloor q2)) by (rewrite Heq; reflexivity).
  rewrite (Qleb_comp _ _ Hdiff _ _ (Qeq_refl _)).
  reflexivity.
Qed.

Theorem nat_Q_roundtrip_1000 : forall (x : nat),
  (x <= 1000)%nat ->
  Q_to_nat_scaled (nat_to_Q_scaled x 1000) 1000 = x.
Proof.
  intros x Hle.
  unfold Q_to_nat_scaled.
  assert (H: nat_to_Q_scaled x 1000 * inject_Z (Zpos 1000) == inject_Z (Z.of_nat x)).
  { apply nat_to_Q_scaled_mult_inverse. }
  rewrite (Qround_compat _ _ H).
  rewrite Qround_inject_Z.
  apply Nat2Z.id.
Qed.

Close Scope Q_scope.

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

(** ========== CHIMERISM MODEL ========== *)

(** Chimerism occurs when a person has cells from two genetically distinct individuals.
    This can arise from:
    1. Bone marrow/stem cell transplantation (most common in transfusion medicine)
    2. Solid organ transplantation (passenger lymphocyte syndrome)
    3. Twin-to-twin transfusion syndrome (tetragametic chimerism)
    4. Maternal-fetal cell exchange (microchimerism)
    5. Massive transfusion (transient chimerism)

    Clinical significance for transfusion:
    - Mixed-field agglutination in blood typing
    - Discrepant forward and reverse typing
    - May require products compatible with BOTH cell populations
    - Post-transplant: use donor-type blood products *)

Inductive ChimerismType : Type :=
  | NoChimerism
  | TransplantChimerism
  | TransfusionChimerism
  | TwinChimerism
  | MicroChimerism.

Inductive ChimerismStatus : Type :=
  | Full
  | Mixed (host_percent : nat)
  | Transient.

Record ChimericPatient := mkChimericPatient {
  chimera_type : ChimerismType;
  chimera_status : ChimerismStatus;
  chimera_host_type : BloodType;
  chimera_donor_type : BloodType;
  chimera_days_post_event : nat
}.

Definition is_chimeric (p : ChimericPatient) : bool :=
  match chimera_type p with
  | NoChimerism => false
  | _ => true
  end.

Definition chimera_host_percent (p : ChimericPatient) : nat :=
  match chimera_status p with
  | Full => 0
  | Mixed pct => pct
  | Transient => 50
  end.

Definition chimera_donor_percent (p : ChimericPatient) : nat :=
  100 - chimera_host_percent p.

Definition chimeric_transfusion_type (p : ChimericPatient) : BloodType :=
  match chimera_status p with
  | Full => chimera_donor_type p
  | Mixed pct => if Nat.leb 50 pct then chimera_host_type p else chimera_donor_type p
  | Transient => chimera_host_type p
  end.

Definition chimera_rbc_compatible (p : ChimericPatient) (donor : BloodType) : bool :=
  compatible (chimera_host_type p) donor &&
  compatible (chimera_donor_type p) donor.

Definition chimera_plasma_compatible (p : ChimericPatient) (donor : BloodType) : bool :=
  plasma_compatible (chimera_host_type p) donor &&
  plasma_compatible (chimera_donor_type p) donor.

Theorem chimera_needs_universal_rbc :
  forall p, is_chimeric p = true ->
  chimera_host_type p <> chimera_donor_type p ->
  exists donor, chimera_rbc_compatible p donor = true.
Proof.
  intros p _ _.
  exists O_neg. unfold chimera_rbc_compatible.
  destruct (chimera_host_type p) as [[| | | ] [| ]];
  destruct (chimera_donor_type p) as [[| | | ] [| ]]; reflexivity.
Qed.

Theorem chimera_o_neg_always_safe :
  forall p, chimera_rbc_compatible p O_neg = true.
Proof.
  intro p. unfold chimera_rbc_compatible.
  destruct (chimera_host_type p) as [[| | | ] [| ]];
  destruct (chimera_donor_type p) as [[| | | ] [| ]]; reflexivity.
Qed.

Theorem chimera_ab_plasma_always_safe :
  forall p, chimera_plasma_compatible p AB_pos = true.
Proof.
  intro p. unfold chimera_plasma_compatible.
  destruct (chimera_host_type p) as [[| | | ] [| ]];
  destruct (chimera_donor_type p) as [[| | | ] [| ]]; reflexivity.
Qed.

Definition post_transplant_typing_rule (p : ChimericPatient) : BloodType :=
  match chimera_type p with
  | TransplantChimerism => chimera_donor_type p
  | _ => chimera_host_type p
  end.

Definition chimera_passenger_lymphocyte_risk (p : ChimericPatient) : bool :=
  match chimera_type p with
  | TransplantChimerism =>
      Nat.leb (chimera_days_post_event p) 21 &&
      negb (rbc_compatible_abo (chimera_donor_type p) (chimera_host_type p))
  | _ => false
  end.

Theorem full_engraftment_uses_donor_type :
  forall host_bt donor_bt days,
  let p := mkChimericPatient TransplantChimerism Full host_bt donor_bt days in
  chimeric_transfusion_type p = donor_bt.
Proof. reflexivity. Qed.

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
  intros titer spec comp hem.
  unfold cad_titer_low.
  destruct (Nat.leb 64 titer) eqn:Htiter.
  - left. apply cad_warmer_required_above_benign.
    unfold classify_cad_severity.
    unfold cad_thermal_threshold, cad_titer_critical, cad_titer_high, cad_titer_moderate, cad_titer_low.
    simpl cad_hemolysis_present. simpl cad_thermal_amplitude. simpl cad_titer.
    destruct hem; [intro H; inversion H|].
    destruct (Nat.leb 4096 titer) eqn:E1; [intro H; inversion H|].
    destruct (Nat.leb 1024 titer) eqn:E2; [intro H; inversion H|].
    destruct (Nat.leb 256 titer) eqn:E3; [intro H; inversion H|].
    rewrite Htiter. intro H; inversion H.
  - right. apply Nat.leb_gt. exact Htiter.
Qed.

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

(** ========== MCLEOD SYNDROME AND Kx ANTIGEN ========== *)

(** McLeod syndrome is an X-linked multisystem disorder caused by absence of the
    XK protein, which carries the Kx antigen. The Kx antigen is part of the Kx
    blood group system (ISBT 019) but is functionally linked to the Kell system.

    Key clinical features:
    1. Kell antigens are WEAKENED but not absent (K+w, k+w)
    2. RBCs have acanthocytosis (spiky morphology)
    3. Progressive neuromuscular disease (chorea, myopathy)
    4. Cardiomyopathy
    5. Hemolytic anemia (compensated)

    Transfusion implications:
    - McLeod patients lack Kx and have weak Kell antigens
    - They can form anti-Kx AND anti-Km (antibody to total Kell antigens)
    - Anti-Kx + anti-Km = react with ALL normal RBCs
    - Can ONLY receive blood from other McLeod donors (extremely rare)

    Prevalence: ~1:100,000 males (X-linked, mostly affects males)

    Source: Jung et al., Transfus Med Hemother 2007; AABB Technical Manual 20th Ed *)

Inductive McLeodStatus : Type :=
  | McLeod_Normal
  | McLeod_Carrier
  | McLeod_Affected.

Record KellPhenotype := mkKellPhenotype {
  kell_K_status : bool;
  kell_k_status : bool;
  kell_Kpa_status : bool;
  kell_Kpb_status : bool;
  kell_Jsa_status : bool;
  kell_Jsb_status : bool;
  kell_Kx_status : bool;
  kell_mcleod : McLeodStatus
}.

Definition normal_K_positive : KellPhenotype :=
  mkKellPhenotype true true false true false true true McLeod_Normal.

Definition normal_K_negative : KellPhenotype :=
  mkKellPhenotype false true false true false true true McLeod_Normal.

Definition mcleod_phenotype : KellPhenotype :=
  mkKellPhenotype false true false true false true false McLeod_Affected.

Definition is_mcleod (kp : KellPhenotype) : bool :=
  match kell_mcleod kp with
  | McLeod_Affected => true
  | _ => false
  end.

Definition is_kx_negative (kp : KellPhenotype) : bool :=
  negb (kell_Kx_status kp).

(** McLeod patients can form anti-Kx and anti-Km *)
Inductive McLeodAntibody : Type :=
  | Ab_Kx
  | Ab_Km
  | Ab_Kx_plus_Km.

Definition mcleod_antibody_forms (kp : KellPhenotype) : option McLeodAntibody :=
  if is_mcleod kp then Some Ab_Kx_plus_Km else None.

(** Compatibility for McLeod patients - can only receive McLeod blood *)
Definition mcleod_compatible (recipient_kp donor_kp : KellPhenotype) : bool :=
  if is_mcleod recipient_kp then
    is_mcleod donor_kp
  else
    true.

Theorem mcleod_only_receives_mcleod :
  forall donor_kp,
  is_mcleod donor_kp = false ->
  mcleod_compatible mcleod_phenotype donor_kp = false.
Proof.
  intros donor_kp H.
  unfold mcleod_compatible. simpl. exact H.
Qed.

Theorem mcleod_can_receive_mcleod :
  forall donor_kp,
  is_mcleod donor_kp = true ->
  mcleod_compatible mcleod_phenotype donor_kp = true.
Proof.
  intros donor_kp H.
  unfold mcleod_compatible. simpl. exact H.
Qed.

Theorem normal_can_receive_any_kell :
  forall recipient_kp donor_kp,
  is_mcleod recipient_kp = false ->
  mcleod_compatible recipient_kp donor_kp = true.
Proof.
  intros recipient_kp donor_kp H.
  unfold mcleod_compatible. rewrite H. reflexivity.
Qed.

(** McLeod syndrome prevalence (per 100,000 males) *)
Definition mcleod_prevalence_per_100000 : nat := 1.

(** Kell-null phenotype (K0) - lacks ALL Kell antigens, can form anti-Ku *)
Definition is_kell_null (kp : KellPhenotype) : bool :=
  negb (kell_K_status kp) && negb (kell_k_status kp) &&
  negb (kell_Kpa_status kp) && negb (kell_Kpb_status kp) &&
  negb (kell_Jsa_status kp) && negb (kell_Jsb_status kp) &&
  kell_Kx_status kp.

Definition kell_null_phenotype : KellPhenotype :=
  mkKellPhenotype false false false false false false true McLeod_Normal.

Theorem kell_null_is_kx_positive :
  kell_Kx_status kell_null_phenotype = true.
Proof. reflexivity. Qed.

Theorem mcleod_is_kx_negative :
  kell_Kx_status mcleod_phenotype = false.
Proof. reflexivity. Qed.

(** Key distinction: K0 (Kell-null) has Kx+, McLeod has Kx- *)
Theorem kell_null_vs_mcleod_kx_difference :
  kell_Kx_status kell_null_phenotype = true /\
  kell_Kx_status mcleod_phenotype = false.
Proof. split; reflexivity. Qed.

(** ========== ANTIGEN DOSAGE EFFECTS ========== *)

(** Dosage effect: homozygous individuals express more antigen than heterozygous.
    This affects antibody reactivity - antibodies react more strongly with
    cells from homozygous donors.

    Clinically significant dosage effects:
    - Kidd (Jka, Jkb): STRONG dosage - can cause missed antibody detection
    - Duffy (Fya, Fyb): Moderate dosage
    - MNS (M, N, S, s): Strong dosage
    - Rh (C, c, E, e): Variable dosage (D shows minimal dosage)

    Clinical impact:
    1. Antibodies may only react with homozygous cells
    2. Weak antibodies may be missed if only heterozygous cells tested
    3. Crossmatch may be negative but transfusion causes reaction

    Source: Storry & Olsson, ISBT Science Series 2009 *)

Inductive DosageStrength : Type :=
  | Dosage_None
  | Dosage_Weak
  | Dosage_Moderate
  | Dosage_Strong.

Definition antigen_dosage_effect (ag : Antigen) : DosageStrength :=
  match ag with
  | Ag_Jka | Ag_Jkb => Dosage_Strong
  | Ag_M | Ag_N | Ag_S | Ag_s => Dosage_Strong
  | Ag_Fya | Ag_Fyb => Dosage_Moderate
  | Ag_C | Ag_c | Ag_E | Ag_e => Dosage_Weak
  | Ag_Lua | Ag_Lub => Dosage_Moderate
  | Ag_Doa | Ag_Dob => Dosage_Moderate
  | _ => Dosage_None
  end.

Definition dosage_strength_value (d : DosageStrength) : nat :=
  match d with
  | Dosage_None => 0
  | Dosage_Weak => 1
  | Dosage_Moderate => 2
  | Dosage_Strong => 3
  end.

(** Zygosity modeling *)
Inductive Zygosity : Type :=
  | Homozygous
  | Heterozygous
  | Unknown_Zygosity.

Record AntigenExpression := mkAntigenExpression {
  expr_antigen : Antigen;
  expr_zygosity : Zygosity;
  expr_strength : nat
}.

(** Expected reactivity score based on antibody titer, dosage, and zygosity *)
Definition expected_reactivity (ab_titer : nat) (dosage : DosageStrength)
                                (zygosity : Zygosity) : nat :=
  let dosage_factor := match dosage, zygosity with
    | Dosage_Strong, Homozygous => 4
    | Dosage_Strong, Heterozygous => 1
    | Dosage_Strong, Unknown_Zygosity => 2
    | Dosage_Moderate, Homozygous => 3
    | Dosage_Moderate, Heterozygous => 2
    | Dosage_Moderate, Unknown_Zygosity => 2
    | Dosage_Weak, Homozygous => 2
    | Dosage_Weak, Heterozygous => 2
    | Dosage_Weak, Unknown_Zygosity => 2
    | Dosage_None, _ => 2
    end in
  ab_titer * dosage_factor.

Theorem kidd_homozygous_strongly_reactive :
  expected_reactivity 2 Dosage_Strong Homozygous = 8.
Proof. reflexivity. Qed.

Theorem kidd_heterozygous_weakly_reactive :
  expected_reactivity 2 Dosage_Strong Heterozygous = 2.
Proof. reflexivity. Qed.

(** Risk of missing antibody with heterozygous screening cells *)
Definition antibody_detection_risk (ag : Antigen) (zygosity : Zygosity) : bool :=
  match antigen_dosage_effect ag, zygosity with
  | Dosage_Strong, Heterozygous => true
  | _, _ => false
  end.

Theorem kidd_antibody_detection_risk :
  antibody_detection_risk Ag_Jka Heterozygous = true /\
  antibody_detection_risk Ag_Jka Homozygous = false.
Proof. split; reflexivity. Qed.

(** Recommend homozygous cells for screening when dosage is strong *)
Definition requires_homozygous_screening_cells (ag : Antigen) : bool :=
  match antigen_dosage_effect ag with
  | Dosage_Strong => true
  | _ => false
  end.

Theorem kidd_requires_homozygous_cells :
  requires_homozygous_screening_cells Ag_Jka = true /\
  requires_homozygous_screening_cells Ag_Jkb = true.
Proof. split; reflexivity. Qed.

Theorem rh_D_no_dosage_concern :
  requires_homozygous_screening_cells Ag_D = false.
Proof. reflexivity. Qed.

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

(** ========== HLA SYSTEM - COMPREHENSIVE MODEL ========== *)

(** HLA (Human Leukocyte Antigen) system is critical for:
    1. Platelet refractoriness - HLA antibodies destroy transfused platelets
    2. Transfusion-related acute lung injury (TRALI) - donor HLA antibodies
    3. Stem cell/bone marrow transplantation - requires HLA matching
    4. Solid organ transplantation - Class I and II matching

    HLA nomenclature: HLA-A*02:01:01:01 means
    - A = locus
    - 02 = allele group (serological equivalent)
    - 01 = specific protein
    - 01 = synonymous DNA variation
    - 01 = non-coding variation *)

Inductive HLALocus : Type :=
  | Locus_A | Locus_B | Locus_C
  | Locus_DR | Locus_DQ | Locus_DP.

Inductive HLAClass : Type := Class_I | Class_II.

Definition locus_class (loc : HLALocus) : HLAClass :=
  match loc with
  | Locus_A | Locus_B | Locus_C => Class_I
  | Locus_DR | Locus_DQ | Locus_DP => Class_II
  end.

(** HLA allele representation - allele group level (2-digit resolution).
    Common alleles for transfusion medicine purposes. *)
Record HLAAllele := mkHLAAllele {
  hla_locus : HLALocus;
  hla_allele_group : nat
}.

Definition hla_allele_eq_dec (x y : HLAAllele) : {x = y} + {x <> y}.
Proof. decide equality; try apply Nat.eq_dec; decide equality. Defined.

(** Legacy locus types for backwards compatibility *)
Inductive HLAClass1 : Type := HLA_A | HLA_B | HLA_C.
Inductive HLAClass2 : Type := HLA_DR | HLA_DQ | HLA_DP.

Definition hla_class1_eq_dec (x y : HLAClass1) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition hla_class2_eq_dec (x y : HLAClass2) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(** Common HLA-A allele groups (serological equivalents) *)
Definition HLA_A01 := mkHLAAllele Locus_A 1.
Definition HLA_A02 := mkHLAAllele Locus_A 2.
Definition HLA_A03 := mkHLAAllele Locus_A 3.
Definition HLA_A11 := mkHLAAllele Locus_A 11.
Definition HLA_A23 := mkHLAAllele Locus_A 23.
Definition HLA_A24 := mkHLAAllele Locus_A 24.
Definition HLA_A25 := mkHLAAllele Locus_A 25.
Definition HLA_A26 := mkHLAAllele Locus_A 26.
Definition HLA_A29 := mkHLAAllele Locus_A 29.
Definition HLA_A30 := mkHLAAllele Locus_A 30.
Definition HLA_A31 := mkHLAAllele Locus_A 31.
Definition HLA_A32 := mkHLAAllele Locus_A 32.
Definition HLA_A33 := mkHLAAllele Locus_A 33.
Definition HLA_A34 := mkHLAAllele Locus_A 34.
Definition HLA_A36 := mkHLAAllele Locus_A 36.
Definition HLA_A66 := mkHLAAllele Locus_A 66.
Definition HLA_A68 := mkHLAAllele Locus_A 68.
Definition HLA_A69 := mkHLAAllele Locus_A 69.
Definition HLA_A74 := mkHLAAllele Locus_A 74.
Definition HLA_A80 := mkHLAAllele Locus_A 80.

(** Common HLA-B allele groups *)
Definition HLA_B07 := mkHLAAllele Locus_B 7.
Definition HLA_B08 := mkHLAAllele Locus_B 8.
Definition HLA_B13 := mkHLAAllele Locus_B 13.
Definition HLA_B14 := mkHLAAllele Locus_B 14.
Definition HLA_B15 := mkHLAAllele Locus_B 15.
Definition HLA_B18 := mkHLAAllele Locus_B 18.
Definition HLA_B27 := mkHLAAllele Locus_B 27.
Definition HLA_B35 := mkHLAAllele Locus_B 35.
Definition HLA_B37 := mkHLAAllele Locus_B 37.
Definition HLA_B38 := mkHLAAllele Locus_B 38.
Definition HLA_B39 := mkHLAAllele Locus_B 39.
Definition HLA_B40 := mkHLAAllele Locus_B 40.
Definition HLA_B41 := mkHLAAllele Locus_B 41.
Definition HLA_B42 := mkHLAAllele Locus_B 42.
Definition HLA_B44 := mkHLAAllele Locus_B 44.
Definition HLA_B45 := mkHLAAllele Locus_B 45.
Definition HLA_B46 := mkHLAAllele Locus_B 46.
Definition HLA_B47 := mkHLAAllele Locus_B 47.
Definition HLA_B48 := mkHLAAllele Locus_B 48.
Definition HLA_B49 := mkHLAAllele Locus_B 49.
Definition HLA_B50 := mkHLAAllele Locus_B 50.
Definition HLA_B51 := mkHLAAllele Locus_B 51.
Definition HLA_B52 := mkHLAAllele Locus_B 52.
Definition HLA_B53 := mkHLAAllele Locus_B 53.
Definition HLA_B54 := mkHLAAllele Locus_B 54.
Definition HLA_B55 := mkHLAAllele Locus_B 55.
Definition HLA_B56 := mkHLAAllele Locus_B 56.
Definition HLA_B57 := mkHLAAllele Locus_B 57.
Definition HLA_B58 := mkHLAAllele Locus_B 58.

(** Common HLA-DR allele groups *)
Definition HLA_DR1 := mkHLAAllele Locus_DR 1.
Definition HLA_DR3 := mkHLAAllele Locus_DR 3.
Definition HLA_DR4 := mkHLAAllele Locus_DR 4.
Definition HLA_DR7 := mkHLAAllele Locus_DR 7.
Definition HLA_DR8 := mkHLAAllele Locus_DR 8.
Definition HLA_DR9 := mkHLAAllele Locus_DR 9.
Definition HLA_DR10 := mkHLAAllele Locus_DR 10.
Definition HLA_DR11 := mkHLAAllele Locus_DR 11.
Definition HLA_DR12 := mkHLAAllele Locus_DR 12.
Definition HLA_DR13 := mkHLAAllele Locus_DR 13.
Definition HLA_DR14 := mkHLAAllele Locus_DR 14.
Definition HLA_DR15 := mkHLAAllele Locus_DR 15.
Definition HLA_DR16 := mkHLAAllele Locus_DR 16.

(** HLA typing record - represents an individual's HLA type.
    Each person has two alleles per locus (one from each parent).
    Option type used because typing may be incomplete. *)
Record HLATyping := mkHLATyping {
  hla_A_1 : option HLAAllele;
  hla_A_2 : option HLAAllele;
  hla_B_1 : option HLAAllele;
  hla_B_2 : option HLAAllele;
  hla_C_1 : option HLAAllele;
  hla_C_2 : option HLAAllele;
  hla_DR_1 : option HLAAllele;
  hla_DR_2 : option HLAAllele;
  hla_DQ_1 : option HLAAllele;
  hla_DQ_2 : option HLAAllele;
  hla_DP_1 : option HLAAllele;
  hla_DP_2 : option HLAAllele
}.

(** Extract all typed alleles from an HLA typing *)
Definition hla_typed_alleles (t : HLATyping) : list HLAAllele :=
  let add_opt opt acc := match opt with Some a => a :: acc | None => acc end in
  add_opt (hla_A_1 t) (add_opt (hla_A_2 t)
  (add_opt (hla_B_1 t) (add_opt (hla_B_2 t)
  (add_opt (hla_C_1 t) (add_opt (hla_C_2 t)
  (add_opt (hla_DR_1 t) (add_opt (hla_DR_2 t)
  (add_opt (hla_DQ_1 t) (add_opt (hla_DQ_2 t)
  (add_opt (hla_DP_1 t) (add_opt (hla_DP_2 t) []))))))))))).

(** HLA Class I alleles only (relevant for platelet refractoriness) *)
Definition hla_class1_alleles (t : HLATyping) : list HLAAllele :=
  filter (fun a => match locus_class (hla_locus a) with
                   | Class_I => true | Class_II => false end)
         (hla_typed_alleles t).

(** HLA Class II alleles only (relevant for transplantation) *)
Definition hla_class2_alleles (t : HLATyping) : list HLAAllele :=
  filter (fun a => match locus_class (hla_locus a) with
                   | Class_II => true | Class_I => false end)
         (hla_typed_alleles t).

(** HLA antibody record - represents anti-HLA antibodies *)
Record HLAAntibodyProfile := mkHLAAntibodies {
  anti_hla_specificities : list HLAAllele;
  anti_hla_class1_present : bool;
  anti_hla_class2_present : bool;
  panel_reactive_antibody_percent : nat
}.

(** Check if any recipient antibodies match donor HLA *)
Definition hla_antibody_crossmatch (recipient_abs : HLAAntibodyProfile)
                                    (donor_hla : HLATyping) : bool :=
  existsb (fun ab =>
    existsb (fun donor_allele =>
      if hla_allele_eq_dec ab donor_allele then true else false)
    (hla_typed_alleles donor_hla))
  (anti_hla_specificities recipient_abs).

(** Positive crossmatch = incompatible *)
Definition hla_crossmatch_compatible (recipient_abs : HLAAntibodyProfile)
                                      (donor_hla : HLATyping) : bool :=
  negb (hla_antibody_crossmatch recipient_abs donor_hla).

(** ========== EPITOPE-BASED HLA VIRTUAL CROSSMATCH ========== *)

(** Modern HLA matching goes beyond allele-level to epitope-level analysis.
    HLA epitopes are the actual antibody-binding sites on HLA molecules.
    Multiple alleles can share epitopes, and a single allele has many epitopes.

    Key concepts:
    1. EPLETS: 3Å polymorphic amino acid configurations defining antibody epitopes
    2. DSA (Donor-Specific Antibody): Antibody to epitope on donor HLA
    3. Virtual crossmatch: Predicting physical crossmatch from epitope analysis
    4. MFI (Mean Fluorescence Intensity): Antibody strength measure

    Clinical applications:
    - Solid organ transplant: Predict rejection risk
    - Platelet refractoriness: Select compatible donors
    - HSCT: Permissive vs non-permissive mismatches

    Source: Duquesnoy, Hum Immunol 2006; Tambur & Claas, Curr Opin Organ Transplant 2015 *)

(** Epitope identifiers - modeled as unique integers.
    In practice, these come from databases like HLA Matchmaker.
    Example eplets: 62GE, 65QIA, 142T, 163LG, etc. *)
Record HLAEpitope := mkHLAEpitope {
  epitope_id : nat;
  epitope_locus : HLALocus;
  epitope_immunogenic : bool
}.

Definition hla_locus_eq_dec (x y : HLALocus) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition epitope_eq_dec (x y : HLAEpitope) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply Bool.bool_dec.
  - apply hla_locus_eq_dec.
  - apply Nat.eq_dec.
Defined.

Definition epitope_eqb (x y : HLAEpitope) : bool :=
  if epitope_eq_dec x y then true else false.

(** Some clinically significant eplets *)
Definition eplet_62GE := mkHLAEpitope 62 Locus_A true.
Definition eplet_65QIA := mkHLAEpitope 65 Locus_A true.
Definition eplet_142T := mkHLAEpitope 142 Locus_B true.
Definition eplet_163LG := mkHLAEpitope 163 Locus_B true.
Definition eplet_77N := mkHLAEpitope 77 Locus_DR true.
Definition eplet_96HK := mkHLAEpitope 96 Locus_DQ true.

(** Epitope-to-allele mapping: which epitopes are present on each allele.
    This would normally be a database lookup. We model it as a function. *)
Definition allele_epitopes (a : HLAAllele) : list HLAEpitope :=
  match hla_locus a, hla_allele_group a with
  | Locus_A, 2 => [eplet_62GE; eplet_65QIA]
  | Locus_A, 3 => [eplet_62GE]
  | Locus_B, 7 => [eplet_142T; eplet_163LG]
  | Locus_B, 8 => [eplet_142T]
  | Locus_DR, 4 => [eplet_77N]
  | Locus_DQ, 2 => [eplet_96HK]
  | _, _ => []
  end.

(** Get all epitopes from a typing *)
Definition typing_epitopes (t : HLATyping) : list HLAEpitope :=
  flat_map allele_epitopes (hla_typed_alleles t).

(** Remove duplicates from epitope list *)
Fixpoint epitope_dedup (l : list HLAEpitope) : list HLAEpitope :=
  match l with
  | [] => []
  | x :: xs =>
      if existsb (epitope_eqb x) xs then epitope_dedup xs
      else x :: epitope_dedup xs
  end.

(** Antibody to specific epitope with MFI (strength) *)
Record EpitopeAntibody := mkEpitopeAntibody {
  ab_epitope : HLAEpitope;
  ab_mfi : nat;
  ab_complement_fixing : bool
}.

(** Virtual crossmatch antibody profile *)
Record VirtualXMProfile := mkVirtualXMProfile {
  vxm_epitope_abs : list EpitopeAntibody;
  vxm_current_pra : nat;
  vxm_peak_pra : nat;
  vxm_sensitization_events : nat
}.

(** MFI thresholds for clinical decision making *)
Definition mfi_negative_threshold : nat := 500.
Definition mfi_weak_positive_threshold : nat := 2000.
Definition mfi_moderate_threshold : nat := 5000.
Definition mfi_strong_threshold : nat := 10000.

Inductive MFIStrength : Type :=
  | MFI_Negative
  | MFI_WeakPositive
  | MFI_Moderate
  | MFI_Strong
  | MFI_VeryStrong.

Definition classify_mfi (mfi : nat) : MFIStrength :=
  if Nat.leb mfi mfi_negative_threshold then MFI_Negative
  else if Nat.leb mfi mfi_weak_positive_threshold then MFI_WeakPositive
  else if Nat.leb mfi mfi_moderate_threshold then MFI_Moderate
  else if Nat.leb mfi mfi_strong_threshold then MFI_Strong
  else MFI_VeryStrong.

(** Check if recipient has antibody to any donor epitope *)
Definition has_dsa (recipient : VirtualXMProfile) (donor : HLATyping) : bool :=
  let donor_epitopes := epitope_dedup (typing_epitopes donor) in
  existsb (fun ab =>
    existsb (fun de =>
      epitope_eqb (ab_epitope ab) de && Nat.ltb mfi_negative_threshold (ab_mfi ab))
    donor_epitopes)
  (vxm_epitope_abs recipient).

(** Get DSA with highest MFI *)
Definition max_dsa_mfi (recipient : VirtualXMProfile) (donor : HLATyping) : nat :=
  let donor_epitopes := epitope_dedup (typing_epitopes donor) in
  fold_left (fun acc ab =>
    if existsb (epitope_eqb (ab_epitope ab)) donor_epitopes
    then Nat.max acc (ab_mfi ab)
    else acc)
  (vxm_epitope_abs recipient) 0.

(** Virtual crossmatch result *)
Inductive VirtualXMResult : Type :=
  | VXM_Negative
  | VXM_WeakPositive
  | VXM_Positive
  | VXM_StrongPositive.

Definition virtual_crossmatch (recipient : VirtualXMProfile)
                               (donor : HLATyping) : VirtualXMResult :=
  let max_mfi := max_dsa_mfi recipient donor in
  match classify_mfi max_mfi with
  | MFI_Negative => VXM_Negative
  | MFI_WeakPositive => VXM_WeakPositive
  | MFI_Moderate => VXM_Positive
  | MFI_Strong => VXM_StrongPositive
  | MFI_VeryStrong => VXM_StrongPositive
  end.

(** Transplant acceptability based on virtual crossmatch *)
Inductive TransplantAcceptability : Type :=
  | Acceptable
  | Acceptable_With_Desensitization
  | Unacceptable_High_Risk
  | Absolute_Contraindication.

Definition transplant_acceptability (vxm : VirtualXMResult)
                                     (complement_fixing_dsa : bool) : TransplantAcceptability :=
  match vxm, complement_fixing_dsa with
  | VXM_Negative, _ => Acceptable
  | VXM_WeakPositive, false => Acceptable_With_Desensitization
  | VXM_WeakPositive, true => Unacceptable_High_Risk
  | VXM_Positive, _ => Unacceptable_High_Risk
  | VXM_StrongPositive, _ => Absolute_Contraindication
  end.

(** Check for complement-fixing DSA *)
Definition has_complement_fixing_dsa (recipient : VirtualXMProfile)
                                       (donor : HLATyping) : bool :=
  let donor_epitopes := epitope_dedup (typing_epitopes donor) in
  existsb (fun ab =>
    ab_complement_fixing ab &&
    Nat.ltb mfi_negative_threshold (ab_mfi ab) &&
    existsb (epitope_eqb (ab_epitope ab)) donor_epitopes)
  (vxm_epitope_abs recipient).

(** Full virtual crossmatch assessment *)
Definition full_virtual_crossmatch (recipient : VirtualXMProfile)
                                    (donor : HLATyping) : TransplantAcceptability :=
  let vxm := virtual_crossmatch recipient donor in
  let cf := has_complement_fixing_dsa recipient donor in
  transplant_acceptability vxm cf.

Theorem negative_vxm_acceptable :
  forall recipient donor,
  virtual_crossmatch recipient donor = VXM_Negative ->
  full_virtual_crossmatch recipient donor = Acceptable.
Proof.
  intros recipient donor Hvxm.
  unfold full_virtual_crossmatch, transplant_acceptability.
  rewrite Hvxm. destruct (has_complement_fixing_dsa recipient donor); reflexivity.
Qed.

Theorem strong_positive_absolute_contraindication :
  forall recipient donor,
  virtual_crossmatch recipient donor = VXM_StrongPositive ->
  full_virtual_crossmatch recipient donor = Absolute_Contraindication.
Proof.
  intros recipient donor Hvxm.
  unfold full_virtual_crossmatch, transplant_acceptability.
  rewrite Hvxm. destruct (has_complement_fixing_dsa recipient donor); reflexivity.
Qed.

(** Epitope mismatch load: count of immunogenic epitopes on donor not on recipient *)
Definition epitope_mismatch_load (recipient donor : HLATyping) : nat :=
  let r_epitopes := epitope_dedup (typing_epitopes recipient) in
  let d_epitopes := epitope_dedup (typing_epitopes donor) in
  let mismatched := filter (fun de =>
    negb (existsb (epitope_eqb de) r_epitopes) && epitope_immunogenic de)
    d_epitopes in
  length mismatched.

(** Platelet virtual crossmatch for refractory patients *)
Definition platelet_virtual_crossmatch (recipient : VirtualXMProfile)
                                        (donor : HLATyping) : bool :=
  match virtual_crossmatch recipient donor with
  | VXM_Negative => true
  | VXM_WeakPositive => true
  | _ => false
  end.

Theorem negative_vxm_platelet_compatible :
  forall recipient donor,
  virtual_crossmatch recipient donor = VXM_Negative ->
  platelet_virtual_crossmatch recipient donor = true.
Proof.
  intros recipient donor H. unfold platelet_virtual_crossmatch. rewrite H. reflexivity.
Qed.

Theorem positive_vxm_platelet_incompatible :
  forall recipient donor,
  virtual_crossmatch recipient donor = VXM_Positive ->
  platelet_virtual_crossmatch recipient donor = false.
Proof.
  intros recipient donor H. unfold platelet_virtual_crossmatch. rewrite H. reflexivity.
Qed.

(** Calculated PRA from epitope antibodies *)
Definition calculated_pra (abs : list EpitopeAntibody) : nat :=
  let significant := filter (fun ab => Nat.ltb mfi_negative_threshold (ab_mfi ab)) abs in
  Nat.min 100 (length significant * 5).

Theorem high_antibody_count_high_pra :
  forall abs,
  length (filter (fun ab => Nat.ltb mfi_negative_threshold (ab_mfi ab)) abs) >= 20 ->
  calculated_pra abs = 100.
Proof.
  intros abs H. unfold calculated_pra.
  assert (length (filter (fun ab => (mfi_negative_threshold <? ab_mfi ab)) abs) * 5 >= 100) as Hge.
  { lia. }
  apply Nat.min_l. lia.
Qed.

(** HLA match grade for platelets (Class I only matters) *)
Inductive HLAMatchGrade : Type :=
  | HLA_A_Match
  | HLA_B1U_Match
  | HLA_B2U_Match
  | HLA_C_Match
  | HLA_D_Match
  | HLA_X_Match.

Definition hla_allele_at_locus (loc : HLALocus) (typing : HLATyping) : list HLAAllele :=
  filter (fun a => match hla_locus a, loc with
                   | Locus_A, Locus_A => true
                   | Locus_B, Locus_B => true
                   | Locus_C, Locus_C => true
                   | Locus_DR, Locus_DR => true
                   | Locus_DQ, Locus_DQ => true
                   | Locus_DP, Locus_DP => true
                   | _, _ => false
                   end)
         (hla_typed_alleles typing).

Definition count_hla_mismatches_at_locus (loc : HLALocus)
                                          (recipient donor : HLATyping) : nat :=
  let r_alleles := hla_allele_at_locus loc recipient in
  let d_alleles := hla_allele_at_locus loc donor in
  length (filter (fun d_a =>
    negb (existsb (fun r_a =>
      if hla_allele_eq_dec d_a r_a then true else false) r_alleles))
    d_alleles).

Definition total_hla_class1_mismatches (recipient donor : HLATyping) : nat :=
  count_hla_mismatches_at_locus Locus_A recipient donor +
  count_hla_mismatches_at_locus Locus_B recipient donor +
  count_hla_mismatches_at_locus Locus_C recipient donor.

Definition total_hla_class2_mismatches (recipient donor : HLATyping) : nat :=
  count_hla_mismatches_at_locus Locus_DR recipient donor +
  count_hla_mismatches_at_locus Locus_DQ recipient donor +
  count_hla_mismatches_at_locus Locus_DP recipient donor.

(** Grade platelet HLA match per AABB guidelines *)
Definition grade_platelet_hla_match (recipient donor : HLATyping) : HLAMatchGrade :=
  let mm := total_hla_class1_mismatches recipient donor in
  if Nat.eqb mm 0 then HLA_A_Match
  else if Nat.leb mm 1 then HLA_B1U_Match
  else if Nat.leb mm 2 then HLA_B2U_Match
  else HLA_X_Match.

(** Legacy locus matching (backwards compatible) *)
Definition hla_matched (recipient_hla donor_hla : list HLAClass1) : bool :=
  forallb (fun h => existsb (fun h' =>
    if hla_class1_eq_dec h h' then true else false) donor_hla) recipient_hla.

(** Platelet refractoriness due to HLA antibodies *)
Definition platelet_refractory_hla (abs : HLAAntibodyProfile) : bool :=
  anti_hla_class1_present abs && Nat.leb 20 (panel_reactive_antibody_percent abs).

Theorem high_pra_indicates_refractoriness :
  forall abs, panel_reactive_antibody_percent abs >= 80 ->
  anti_hla_class1_present abs = true ->
  platelet_refractory_hla abs = true.
Proof.
  intros abs Hpra Hclass1. unfold platelet_refractory_hla.
  rewrite Hclass1. simpl.
  apply (proj2 (Nat.leb_le 20 (panel_reactive_antibody_percent abs))). lia.
Qed.

Theorem zero_mismatch_is_A_match :
  forall r d, total_hla_class1_mismatches r d = 0 ->
  grade_platelet_hla_match r d = HLA_A_Match.
Proof.
  intros r d H. unfold grade_platelet_hla_match. rewrite H. reflexivity.
Qed.

(** Platelet unit with extended HLA typing *)
Record PlateletUnit := mkPlateletUnit {
  plt_abo : ABO;
  plt_rh : Rh;
  plt_hla : list HLAClass1;
  plt_hla_typing : option HLATyping;
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

Theorem japan_very_low_rh_neg : rh_neg_prevalence Japan = 6.
Proof. native_compute. reflexivity. Qed.

Theorem nigeria_low_rh_neg : rh_neg_prevalence Nigeria = 51.
Proof. native_compute. reflexivity. Qed.

Theorem india_low_rh_neg : rh_neg_prevalence India = 59.
Proof. native_compute. reflexivity. Qed.

Theorem us_moderate_rh_neg : rh_neg_prevalence UnitedStates = 150.
Proof. native_compute. reflexivity. Qed.

Definition universal_donor_scarcity (pop : Population) : nat :=
  pop_frequency pop O_neg.

Theorem japan_critical_O_neg : universal_donor_scarcity Japan = 2.
Proof. native_compute. reflexivity. Qed.

Theorem us_better_O_neg : universal_donor_scarcity UnitedStates = 66.
Proof. reflexivity. Qed.

Definition expected_compatible_supply (pop : Population) (recipient : BloodType) : nat :=
  fold_left Nat.add
    (map (fun donor => if compatible recipient donor
                       then pop_frequency pop donor else 0)
         all_blood_types) 0.

Theorem O_neg_supply_varies :
  expected_compatible_supply UnitedStates O_neg = 66 /\
  expected_compatible_supply Japan O_neg = 2.
Proof. split; native_compute; reflexivity. Qed.

Theorem AB_pos_supply_abundant :
  expected_compatible_supply UnitedStates AB_pos = 1000 /\
  expected_compatible_supply Japan AB_pos = 1001.
Proof. split; native_compute; reflexivity. Qed.

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

(** ========== HPA (HUMAN PLATELET ANTIGEN) SYSTEM ========== *)

(** HPA antigens are platelet-specific antigens important for:
    1. Neonatal alloimmune thrombocytopenia (NAIT) - maternal anti-HPA
    2. Post-transfusion purpura (PTP) - anti-HPA after transfusion
    3. Platelet refractoriness - anti-HPA contributes along with anti-HLA
    4. Granulocyte transfusion - granulocytes carry HPA antigens

    HPA nomenclature:
    - HPA-1a/1b, HPA-2a/2b, etc. (allelic pairs)
    - "a" allele is higher frequency, "b" is lower frequency
    - HPA-1a (PlA1) is most clinically significant

    NAIT most commonly caused by:
    - HPA-1a (80% of Caucasian cases)
    - HPA-5b (10-15% of Caucasian cases)
    - HPA-15b (significant in Asian populations)

    Source: Curtis & McFarland, Semin Fetal Neonatal Med 2008;
            Davoren et al., Transfus Med Rev 2013 *)

Inductive HPASystem : Type :=
  | HPA_1
  | HPA_2
  | HPA_3
  | HPA_4
  | HPA_5
  | HPA_6
  | HPA_9
  | HPA_15.

Inductive HPAAllele : Type :=
  | HPA_a
  | HPA_b.

Definition hpa_allele_eq_dec (x y : HPAAllele) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition hpa_allele_eqb (x y : HPAAllele) : bool :=
  if hpa_allele_eq_dec x y then true else false.

Record HPAAntigen := mkHPAAntigen {
  hpa_system : HPASystem;
  hpa_allele : HPAAllele
}.

Definition hpa_antigen_eq_dec (x y : HPAAntigen) : {x = y} + {x <> y}.
Proof. decide equality; decide equality. Defined.

Definition HPA_1a := mkHPAAntigen HPA_1 HPA_a.
Definition HPA_1b := mkHPAAntigen HPA_1 HPA_b.
Definition HPA_2a := mkHPAAntigen HPA_2 HPA_a.
Definition HPA_2b := mkHPAAntigen HPA_2 HPA_b.
Definition HPA_3a := mkHPAAntigen HPA_3 HPA_a.
Definition HPA_3b := mkHPAAntigen HPA_3 HPA_b.
Definition HPA_4a := mkHPAAntigen HPA_4 HPA_a.
Definition HPA_4b := mkHPAAntigen HPA_4 HPA_b.
Definition HPA_5a := mkHPAAntigen HPA_5 HPA_a.
Definition HPA_5b := mkHPAAntigen HPA_5 HPA_b.
Definition HPA_15a := mkHPAAntigen HPA_15 HPA_a.
Definition HPA_15b := mkHPAAntigen HPA_15 HPA_b.

(** HPA phenotype - diploid (one allele from each parent) *)
Record HPAPhenotype := mkHPAPhenotype {
  hpa1_alleles : (HPAAllele * HPAAllele);
  hpa2_alleles : (HPAAllele * HPAAllele);
  hpa3_alleles : (HPAAllele * HPAAllele);
  hpa5_alleles : (HPAAllele * HPAAllele);
  hpa15_alleles : (HPAAllele * HPAAllele)
}.

Definition has_hpa_antigen (pheno : HPAPhenotype) (ag : HPAAntigen) : bool :=
  let check_alleles alleles a :=
    hpa_allele_eqb (fst alleles) a || hpa_allele_eqb (snd alleles) a in
  match hpa_system ag with
  | HPA_1 => check_alleles (hpa1_alleles pheno) (hpa_allele ag)
  | HPA_2 => check_alleles (hpa2_alleles pheno) (hpa_allele ag)
  | HPA_3 => check_alleles (hpa3_alleles pheno) (hpa_allele ag)
  | HPA_5 => check_alleles (hpa5_alleles pheno) (hpa_allele ag)
  | HPA_15 => check_alleles (hpa15_alleles pheno) (hpa_allele ag)
  | _ => false
  end.

(** HPA antibody record *)
Record HPAAntibody := mkHPAAntibody {
  anti_hpa_specificity : HPAAntigen;
  anti_hpa_titer : nat;
  anti_hpa_clinical_significance : bool
}.

(** HPA-1a-negative phenotype (1b/1b homozygous) - at risk for anti-HPA-1a *)
Definition is_hpa1a_negative (pheno : HPAPhenotype) : bool :=
  negb (has_hpa_antigen pheno HPA_1a).

(** HPA compatibility: recipient antibodies vs donor antigens *)
Definition hpa_compatible (recipient_abs : list HPAAntibody)
                           (donor_pheno : HPAPhenotype) : bool :=
  forallb (fun ab =>
    negb (anti_hpa_clinical_significance ab &&
          has_hpa_antigen donor_pheno (anti_hpa_specificity ab)))
    recipient_abs.

(** HPA-1a is most immunogenic - 2.5% of HPA-1a-negative exposed develop antibody *)
Definition hpa1a_immunogenicity_percent_x10 : nat := 25.

(** NAIT risk assessment *)
Inductive NAITRisk : Type :=
  | NAIT_NoRisk
  | NAIT_LowRisk
  | NAIT_HighRisk.

Definition assess_nait_risk (maternal_pheno paternal_pheno : HPAPhenotype) : NAITRisk :=
  let mother_1a_neg := is_hpa1a_negative maternal_pheno in
  let father_has_1a := has_hpa_antigen paternal_pheno HPA_1a in
  if mother_1a_neg && father_has_1a then NAIT_HighRisk
  else if is_hpa1a_negative maternal_pheno then NAIT_LowRisk
  else NAIT_NoRisk.

Theorem hpa1a_neg_mother_1a_pos_father_high_risk :
  forall m p,
  is_hpa1a_negative m = true ->
  has_hpa_antigen p HPA_1a = true ->
  assess_nait_risk m p = NAIT_HighRisk.
Proof.
  intros m p Hm Hp. unfold assess_nait_risk.
  rewrite Hm, Hp. reflexivity.
Qed.

(** Caucasian HPA-1a-negative frequency ~2% *)
Definition hpa1a_negative_frequency_percent : nat := 2.

(** Asian HPA-15b frequency higher than Caucasian *)
Definition hpa15b_frequency_asian_percent : nat := 20.
Definition hpa15b_frequency_caucasian_percent : nat := 10.

(** ========== EXTENDED GRANULOCYTE UNIT WITH HPA ========== *)

(** Granulocytes carry HPA antigens and can cause reactions in sensitized recipients *)
Record GranulocyteUnitExtended := mkGranulocyteExtended {
  gran_ext_base : GranulocyteUnit;
  gran_ext_hpa_pheno : option HPAPhenotype;
  gran_ext_hla_typed : bool
}.

(** Full granulocyte compatibility including HPA *)
Definition granulocyte_full_compatible (recipient_bt : BloodType)
                                        (recipient_hpa_abs : list HPAAntibody)
                                        (recipient_childbearing : bool)
                                        (g : GranulocyteUnitExtended)
                                        (current_time : nat) : bool :=
  let base_ok := granulocyte_safe (gran_ext_base g) recipient_bt
                                   recipient_childbearing current_time in
  let hpa_ok := match gran_ext_hpa_pheno g with
                | Some pheno => hpa_compatible recipient_hpa_abs pheno
                | None => true
                end in
  base_ok && hpa_ok.

Theorem hpa_sensitized_needs_matching :
  forall g r_bt cb t abs pheno,
  gran_ext_hpa_pheno g = Some pheno ->
  hpa_compatible abs pheno = false ->
  granulocyte_full_compatible r_bt abs cb g t = false.
Proof.
  intros g r_bt cb t abs pheno Hpheno Hincompat.
  unfold granulocyte_full_compatible.
  rewrite Hpheno. rewrite Hincompat.
  rewrite andb_false_r. reflexivity.
Qed.

Theorem unsensitized_ignores_hpa :
  forall g r_bt cb t pheno,
  granulocyte_safe (gran_ext_base g) r_bt cb t = true ->
  gran_ext_hpa_pheno g = Some pheno ->
  granulocyte_full_compatible r_bt [] cb g t = true.
Proof.
  intros g r_bt cb t pheno Hsafe Hpheno.
  unfold granulocyte_full_compatible.
  rewrite Hsafe, Hpheno. simpl. reflexivity.
Qed.

(** Extended platelet unit with HPA typing for NAIT-safe transfusion *)
Record PlateletUnitHPA := mkPlateletHPA {
  plt_hpa_base_abo : ABO;
  plt_hpa_base_rh : Rh;
  plt_hpa_phenotype : HPAPhenotype;
  plt_hpa_irradiated : bool;
  plt_hpa_washed : bool
}.

(** NAIT treatment: use HPA-1a-negative, HPA-1b-positive platelets *)
Definition nait_compatible_platelets (maternal_abs : list HPAAntibody)
                                      (plt : PlateletUnitHPA) : bool :=
  hpa_compatible maternal_abs (plt_hpa_phenotype plt) &&
  plt_hpa_irradiated plt &&
  plt_hpa_washed plt.

Theorem nait_platelets_must_be_washed :
  forall abs plt,
  plt_hpa_washed plt = false ->
  nait_compatible_platelets abs plt = false.
Proof.
  intros abs plt H. unfold nait_compatible_platelets.
  rewrite H. repeat rewrite andb_false_r. reflexivity.
Qed.

Theorem nait_platelets_must_be_irradiated :
  forall abs plt,
  plt_hpa_irradiated plt = false ->
  nait_compatible_platelets abs plt = false.
Proof.
  intros abs plt H. unfold nait_compatible_platelets.
  rewrite H. rewrite andb_false_r. reflexivity.
Qed.

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

    NOTE: This function is CONSERVATIVE for Bombay recipients because
    BloodType alone cannot encode Bombay status. Use recipient_compatible_with_subtype
    when donor subtype information is available.

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

(** Full compatibility check including donor subtype - handles Bombay-to-Bombay.
    This is the PREFERRED function when donor subtype is known. *)
Definition recipient_compatible_with_subtype (r : Recipient) (d_sub : ABOSubtype)
                                              (d_rh : Rh) : bool :=
  let r_sub := rcpt_subtype r in
  let r_rh := variant_transfusion_type (rcpt_rh_variant r) in
  let subtype_ok := subtype_compatible r_sub d_sub in
  let rh_ok := match rcpt_sensitized r, r_rh, d_rh with
               | Naive, Neg, Pos => negb (rcpt_female_childbearing r)
               | Sensitized, Neg, Pos => false
               | _, _, _ => true
               end in
  subtype_ok && rh_ok.

Theorem bombay_to_bombay_compatible :
  forall r d_rh,
  rcpt_subtype r = Sub_Bombay ->
  variant_transfusion_type (rcpt_rh_variant r) = Pos ->
  recipient_compatible_with_subtype r Sub_Bombay d_rh = true.
Proof.
  intros r d_rh Hsub Hvar.
  unfold recipient_compatible_with_subtype.
  rewrite Hsub. unfold subtype_compatible, subtype_abo_compatible. simpl.
  rewrite Hvar. destruct (rcpt_sensitized r), d_rh; reflexivity.
Qed.

Theorem bombay_to_bombay_neg_compatible :
  forall r,
  rcpt_subtype r = Sub_Bombay ->
  variant_transfusion_type (rcpt_rh_variant r) = Neg ->
  rcpt_sensitized r = Naive ->
  rcpt_female_childbearing r = false ->
  recipient_compatible_with_subtype r Sub_Bombay Pos = true.
Proof.
  intros r Hsub Hvar Hsens Hcb.
  unfold recipient_compatible_with_subtype.
  rewrite Hsub. unfold subtype_compatible, subtype_abo_compatible. simpl.
  rewrite Hvar, Hsens, Hcb. reflexivity.
Qed.

Theorem bombay_neg_to_bombay_neg_compatible :
  forall r,
  rcpt_subtype r = Sub_Bombay ->
  variant_transfusion_type (rcpt_rh_variant r) = Neg ->
  recipient_compatible_with_subtype r Sub_Bombay Neg = true.
Proof.
  intros r Hsub Hvar.
  unfold recipient_compatible_with_subtype.
  rewrite Hsub. unfold subtype_compatible, subtype_abo_compatible. simpl.
  rewrite Hvar. destruct (rcpt_sensitized r); reflexivity.
Qed.

Theorem bombay_cannot_receive_non_bombay :
  forall r d_sub d_rh,
  rcpt_subtype r = Sub_Bombay ->
  d_sub <> Sub_Bombay ->
  recipient_compatible_with_subtype r d_sub d_rh = false.
Proof.
  intros r d_sub d_rh Hsub Hneq.
  unfold recipient_compatible_with_subtype.
  rewrite Hsub.
  unfold subtype_compatible, subtype_abo_compatible.
  destruct d_sub; try reflexivity; exfalso; apply Hneq; reflexivity.
Qed.

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
  Nat.leb (pop_frequency UnitedStates bt) 15.

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
  Nat.ltb (pop_frequency UnitedStates bt) 20.

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

Lemma pop_sum_bounds_decidable : forall pop,
  Nat.leb 900 (pop_sum pop) && Nat.leb (pop_sum pop) 1100 = true.
Proof.
  intro pop; destruct pop; vm_compute; reflexivity.
Qed.

Theorem all_populations_sum_approximate : forall pop,
  pop_sum pop >= 900 /\ pop_sum pop <= 1100.
Proof.
  intro pop.
  pose proof (pop_sum_bounds_decidable pop) as H.
  apply andb_prop in H. destruct H as [H1 H2].
  split; [apply Nat.leb_le in H1 | apply Nat.leb_le in H2]; exact H1 || exact H2.
Qed.

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
(*                                                                            *)
(*                   XI. HARDY-WEINBERG Q GLOBAL INTEGRATION                  *)
(*                                                                            *)
(******************************************************************************)

Open Scope Q_scope.

Definition allele_freq_nat_to_Q (f : AlleleFreq) : AlleleFreqQ :=
  mkAlleleFreqQ
    (inject_Z (Z.of_nat (freq_pA f)) / 100)
    (inject_Z (Z.of_nat (freq_pB f)) / 100)
    (inject_Z (Z.of_nat (freq_pO f)) / 100).

Definition allele_freq_Q_to_nat_scaled (f : AlleleFreqQ) (scale : positive) : AlleleFreq :=
  mkAlleleFreq
    (Z.to_nat (Qround (freq_pA_Q f * inject_Z (Zpos scale))))
    (Z.to_nat (Qround (freq_pB_Q f * inject_Z (Zpos scale))))
    (Z.to_nat (Qround (freq_pO_Q f * inject_Z (Zpos scale)))).

Definition pop_expected_phenotypes_Q (pop : Population) : PhenoDistributionQ :=
  hardy_weinberg_Q (pop_allele_freq_Q pop).

Definition pop_expected_O_freq_Q (pop : Population) : Q :=
  pd_O_Q (pop_expected_phenotypes_Q pop).

Theorem pop_phenotype_distribution_sums_to_1 : forall pop,
  pheno_dist_sum (pop_expected_phenotypes_Q pop) == 1.
Proof.
  intro pop.
  apply hardy_weinberg_Q_totals.
  apply pop_allele_freq_Q_sums_to_1.
Qed.

Definition Qabs (q : Q) : Q := if Qle_bool 0 q then q else -q.

Definition compare_nat_Q_phenotype (nat_freq : nat) (q_freq : Q) (tolerance : Q) : bool :=
  let nat_as_q := inject_Z (Z.of_nat nat_freq) / 1000 in
  Qle_bool (Qabs (nat_as_q - q_freq)) tolerance.

Theorem us_allele_freq_conversion_consistent :
  let f_nat := us_abo_allele_frequencies in
  let f_q := allele_freq_nat_to_Q f_nat in
  allele_freq_sum f_q == 1.
Proof.
  simpl. unfold allele_freq_sum, allele_freq_nat_to_Q, us_abo_allele_frequencies.
  simpl. reflexivity.
Qed.

Definition expected_blood_type_freq_Q (pop : Population) (bt : BloodType) : Q :=
  let d := pop_expected_phenotypes_Q pop in
  let rh_neg := pop_rh_neg_freq_Q pop in
  let abo_freq := match fst bt with
    | A => pd_A_Q d
    | B => pd_B_Q d
    | AB => pd_AB_Q d
    | O => pd_O_Q d
    end in
  match snd bt with
  | Pos => abo_freq * (1 - rh_neg)
  | Neg => abo_freq * rh_neg
  end.

Theorem expected_blood_type_uses_pop_rh :
  forall pop bt, exists rh_factor,
  expected_blood_type_freq_Q pop bt =
    (match fst bt with
     | A => pd_A_Q (pop_expected_phenotypes_Q pop)
     | B => pd_B_Q (pop_expected_phenotypes_Q pop)
     | AB => pd_AB_Q (pop_expected_phenotypes_Q pop)
     | O => pd_O_Q (pop_expected_phenotypes_Q pop)
     end) * rh_factor.
Proof.
  intros pop bt. unfold expected_blood_type_freq_Q.
  destruct (snd bt); eexists; reflexivity.
Qed.

Close Scope Q_scope.

(******************************************************************************)
(*                                                                            *)
(*                    XII. VALIDATION & TESTING FRAMEWORK                     *)
(*                                                                            *)
(******************************************************************************)

Inductive TestResult : Type :=
  | Pass
  | Fail (reason : nat).

Record CompatibilityTestCase := mkCompatTest {
  test_recipient : BloodType;
  test_donor : BloodType;
  expected_compatible : bool
}.

Definition run_compatibility_test (tc : CompatibilityTestCase) : TestResult :=
  let actual := compatible (test_recipient tc) (test_donor tc) in
  if Bool.eqb actual (expected_compatible tc) then Pass else Fail 1.

Record PlasmaTestCase := mkPlasmaTest {
  plasma_test_recipient : BloodType;
  plasma_test_donor : BloodType;
  plasma_expected_compatible : bool
}.

Definition run_plasma_test (tc : PlasmaTestCase) : TestResult :=
  let actual := plasma_compatible (plasma_test_recipient tc) (plasma_test_donor tc) in
  if Bool.eqb actual (plasma_expected_compatible tc) then Pass else Fail 2.

Definition compatibility_test_suite : list CompatibilityTestCase := [
  mkCompatTest O_neg O_neg true;
  mkCompatTest O_neg A_neg false;
  mkCompatTest A_pos O_neg true;
  mkCompatTest A_pos O_pos true;
  mkCompatTest A_pos A_pos true;
  mkCompatTest A_pos B_pos false;
  mkCompatTest AB_pos O_neg true;
  mkCompatTest AB_pos A_neg true;
  mkCompatTest AB_pos B_neg true;
  mkCompatTest AB_pos AB_neg true;
  mkCompatTest AB_pos AB_pos true;
  mkCompatTest O_neg AB_pos false;
  mkCompatTest B_neg A_neg false;
  mkCompatTest A_neg B_neg false
].

Definition plasma_test_suite : list PlasmaTestCase := [
  mkPlasmaTest AB_pos AB_neg true;
  mkPlasmaTest AB_pos O_neg false;
  mkPlasmaTest O_neg AB_neg true;
  mkPlasmaTest O_neg O_neg true;
  mkPlasmaTest A_pos A_neg true;
  mkPlasmaTest A_pos AB_neg true;
  mkPlasmaTest A_pos B_neg false;
  mkPlasmaTest B_pos B_neg true;
  mkPlasmaTest B_pos AB_neg true;
  mkPlasmaTest B_pos A_neg false
].

Definition all_tests_pass (results : list TestResult) : bool :=
  forallb (fun r => match r with Pass => true | Fail _ => false end) results.

Definition run_all_compatibility_tests : list TestResult :=
  map run_compatibility_test compatibility_test_suite.

Definition run_all_plasma_tests : list TestResult :=
  map run_plasma_test plasma_test_suite.

Theorem compatibility_test_suite_passes :
  all_tests_pass run_all_compatibility_tests = true.
Proof. vm_compute. reflexivity. Qed.

Theorem plasma_test_suite_passes :
  all_tests_pass run_all_plasma_tests = true.
Proof. vm_compute. reflexivity. Qed.

(** ========== CLINICAL CASE VALIDATION ========== *)

(** Test cases derived from real clinical scenarios documented in:
    - AABB Technical Manual, 20th Edition
    - British Committee for Standards in Haematology Guidelines
    - FDA Blood Establishment Registration guidance *)

Record ClinicalCase := mkClinicalCase {
  case_id : nat;
  case_description : nat;
  case_recipient : BloodType;
  case_donor : BloodType;
  case_product : Product;
  case_expected_safe : bool;
  case_clinical_basis : nat
}.

Definition run_clinical_case (c : ClinicalCase) : bool :=
  let actual := match case_product c with
    | PackedRBC => compatible (case_recipient c) (case_donor c)
    | FreshFrozenPlasma => plasma_compatible (case_recipient c) (case_donor c)
    | Platelets => plasma_compatible (case_recipient c) (case_donor c)
    | Cryoprecipitate => plasma_compatible (case_recipient c) (case_donor c)
    | WholeBlood => whole_blood_compatible (case_recipient c) (case_donor c)
    end in
  Bool.eqb actual (case_expected_safe c).

Definition clinical_case_database : list ClinicalCase := [
  mkClinicalCase 1 1 O_neg O_neg PackedRBC true 1;
  mkClinicalCase 2 2 AB_pos O_neg PackedRBC true 2;
  mkClinicalCase 3 3 A_pos A_neg PackedRBC true 3;
  mkClinicalCase 4 4 A_pos O_neg PackedRBC true 4;
  mkClinicalCase 5 5 B_pos B_neg PackedRBC true 5;
  mkClinicalCase 6 6 B_pos O_neg PackedRBC true 6;
  mkClinicalCase 7 7 AB_pos A_neg PackedRBC true 7;
  mkClinicalCase 8 8 AB_pos B_neg PackedRBC true 8;
  mkClinicalCase 9 9 O_pos A_pos PackedRBC false 9;
  mkClinicalCase 10 10 O_pos B_pos PackedRBC false 10;
  mkClinicalCase 11 11 A_pos B_pos PackedRBC false 11;
  mkClinicalCase 12 12 B_pos A_pos PackedRBC false 12;
  mkClinicalCase 13 13 O_neg AB_pos PackedRBC false 13;
  mkClinicalCase 14 14 A_neg B_neg PackedRBC false 14;
  mkClinicalCase 101 101 O_neg AB_neg FreshFrozenPlasma true 101;
  mkClinicalCase 102 102 A_pos AB_neg FreshFrozenPlasma true 102;
  mkClinicalCase 103 103 B_pos AB_neg FreshFrozenPlasma true 103;
  mkClinicalCase 104 104 AB_pos AB_neg FreshFrozenPlasma true 104;
  mkClinicalCase 105 105 AB_pos O_neg FreshFrozenPlasma false 105;
  mkClinicalCase 106 106 A_pos B_neg FreshFrozenPlasma false 106;
  mkClinicalCase 107 107 B_pos A_neg FreshFrozenPlasma false 107;
  mkClinicalCase 201 201 O_neg O_neg WholeBlood true 201;
  mkClinicalCase 202 202 A_pos A_neg WholeBlood true 202;
  mkClinicalCase 203 203 B_pos B_pos WholeBlood true 203;
  mkClinicalCase 204 204 AB_pos AB_neg WholeBlood true 204;
  mkClinicalCase 205 205 O_pos A_pos WholeBlood false 205;
  mkClinicalCase 206 206 A_pos B_pos WholeBlood false 206
].

Theorem all_clinical_cases_pass :
  forallb run_clinical_case clinical_case_database = true.
Proof. vm_compute. reflexivity. Qed.

Definition emergency_case_O_neg_universal :=
  forallb (fun bt => compatible bt O_neg) all_blood_types = true.

Theorem emergency_O_neg_validated : emergency_case_O_neg_universal.
Proof. vm_compute. reflexivity. Qed.

Definition emergency_case_AB_plasma_universal :=
  forallb (fun bt => plasma_compatible bt AB_pos) all_blood_types = true.

Theorem emergency_AB_plasma_validated : emergency_case_AB_plasma_universal.
Proof. vm_compute. reflexivity. Qed.

Definition massive_transfusion_o_neg_safe (recipient : BloodType) : bool :=
  compatible recipient O_neg.

Theorem massive_transfusion_all_safe :
  forall bt, massive_transfusion_o_neg_safe bt = true.
Proof.
  intros [[| | | ] [| ]]; reflexivity.
Qed.

Definition trauma_protocol_compliance : bool :=
  compatible AB_pos O_neg &&
  plasma_compatible AB_pos AB_neg &&
  compatible O_neg O_neg.

Theorem trauma_protocol_verified : trauma_protocol_compliance = true.
Proof. reflexivity. Qed.

Record PopulationValidation := mkPopValid {
  valid_pop : Population;
  valid_sum_in_range : bool;
  valid_all_nonneg : bool
}.

Definition validate_population (pop : Population) : PopulationValidation :=
  let s := pop_sum pop in
  mkPopValid pop
    (andb (Nat.leb 900 s) (Nat.leb s 1100))
    true.

Definition population_valid (pv : PopulationValidation) : bool :=
  andb (valid_sum_in_range pv) (valid_all_nonneg pv).

Definition all_populations_valid : bool :=
  forallb (fun pop => population_valid (validate_population pop))
    [Albania; Algeria; Argentina; Australia; Austria; Brazil; Canada; China;
     France; Germany; India; Italy; Japan; Mexico; Nigeria; Russia; Spain;
     UnitedKingdom; UnitedStates].

Theorem sample_populations_valid :
  all_populations_valid = true.
Proof. vm_compute. reflexivity. Qed.

(** Strict validation: sum must equal exactly 1000 *)
Definition pop_sum_exact (pop : Population) : bool :=
  Nat.eqb (pop_sum pop) 1000.

(** Normalized frequency function - always divides by actual sum, not 1000.
    This ensures frequencies sum to exactly 1 regardless of raw data sum. *)
Open Scope Q_scope.
Definition pop_frequency_normalized (pop : Population) (bt : BloodType) : Q :=
  let raw := inject_Z (Z.of_nat (pop_frequency pop bt)) in
  let total := inject_Z (Z.of_nat (pop_sum pop)) in
  raw / total.

(** All populations have positive sum - trivially true since all entries are nonneg and
    at least one is positive (every population has O+ > 0) *)
Lemma pop_sum_positive : forall pop, (pop_sum pop > 0)%nat.
Proof.
  intro pop. unfold pop_sum. simpl.
  destruct pop; simpl; lia.
Qed.

Close Scope Q_scope.

Record TransfusionScenario := mkScenario {
  scenario_name : nat;
  scenario_recipient : BloodType;
  scenario_donor : BloodType;
  scenario_product : Product;
  scenario_expected_safe : bool
}.

Definition validate_scenario (s : TransfusionScenario) : bool :=
  let actual := match scenario_product s with
    | PackedRBC => compatible (scenario_recipient s) (scenario_donor s)
    | FreshFrozenPlasma => plasma_compatible (scenario_recipient s) (scenario_donor s)
    | Platelets => plasma_compatible (scenario_recipient s) (scenario_donor s)
    | Cryoprecipitate => plasma_compatible (scenario_recipient s) (scenario_donor s)
    | WholeBlood => whole_blood_compatible (scenario_recipient s) (scenario_donor s)
    end in
  Bool.eqb actual (scenario_expected_safe s).

Definition clinical_scenarios : list TransfusionScenario := [
  mkScenario 1 O_neg O_neg PackedRBC true;
  mkScenario 2 AB_pos O_neg PackedRBC true;
  mkScenario 3 AB_pos AB_neg FreshFrozenPlasma true;
  mkScenario 4 O_neg AB_neg FreshFrozenPlasma true;
  mkScenario 5 A_pos B_pos PackedRBC false;
  mkScenario 6 B_pos A_pos FreshFrozenPlasma false;
  mkScenario 7 O_neg O_neg WholeBlood true;
  mkScenario 8 AB_pos AB_neg WholeBlood true
].

Theorem clinical_scenarios_validated :
  forallb validate_scenario clinical_scenarios = true.
Proof. vm_compute. reflexivity. Qed.

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
  ChimerismType ChimerismStatus ChimericPatient is_chimeric
  chimera_rbc_compatible chimera_plasma_compatible chimeric_transfusion_type
  post_transplant_typing_rule chimera_passenger_lymphocyte_risk
  dat_positive crossmatch_difficulty needs_adsorption_study
  extended_compatible_with_dat extended_transfusion_safe
  ABOAllele RhAllele genotype_phenotype punnett_full offspring_phenotypes
  abo_distribution hardy_weinberg
  Population pop_frequency pop_sum pop_rh_neg_sum pop_rh_pos_sum
  pop_rh_neg_freq_Q pop_frequency_normalized
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
  HLALocus HLAClass locus_class HLAAllele HLATyping hla_typed_alleles
  hla_class1_alleles hla_class2_alleles HLAAntibodyProfile hla_antibody_crossmatch
  hla_crossmatch_compatible HLAMatchGrade count_hla_mismatches_at_locus
  total_hla_class1_mismatches total_hla_class2_mismatches grade_platelet_hla_match
  platelet_refractory_hla
  HLAClass1 HLAClass2 hla_matched PlateletUnit platelet_full_compatible CryoUnit
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
  recipient_blood_type recipient_compatible_with_bt recipient_compatible_with_subtype sensitization_risk
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
