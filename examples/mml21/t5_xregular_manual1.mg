Theorem t5_xregular:
 forall v1_xboole_0:set -> prop,
 forall k3_tarski:set -> set,
 forall esk19_1:set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk7_3:set -> set -> set -> set,
 forall esk20_1:set -> set,
 forall esk12_1:set -> set,
 forall esk9_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk15_2:set -> set -> set,
 forall esk21_2:set -> set -> set,
 forall esk5_1:set -> set,
 forall esk4_1:set -> set,
 forall k1_xboole_0:set,
 forall esk10_0:set,
 forall esk11_0:set,
 forall esk22_1:set -> set,
 forall esk3_1:set -> set,
 forall esk2_1:set -> set,
 forall esk1_0:set,
 forall esk23_2:set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall esk18_2:set -> set -> set,
 forall esk17_2:set -> set -> set,
 forall esk16_1:set -> set,
 forall esk8_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X1 X2 -> False) -> (r2_hidden X1 (esk19_1 X2) -> False) -> r2_hidden X1 (k3_tarski (k3_tarski (k3_tarski (k3_tarski X2)))) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk8_2 X1 X2) X3 -> r2_hidden (esk8_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk7_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk7_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X3 X2 -> False) -> (r2_hidden X1 (esk20_1 X2) -> False) -> r2_hidden X3 X1 -> r2_hidden X1 (k3_tarski (k3_tarski (k3_tarski X2))) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski (k3_tarski (k3_tarski (k3_tarski X2)))) -> False) -> r2_hidden X1 (esk19_1 X2) -> False)
  -> (forall X3 X5 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X3 X2 -> False) -> (r2_hidden X1 (esk12_1 X2) -> False) -> r2_hidden X5 X1 -> r2_hidden X4 X5 -> r2_hidden X3 X4 -> r2_hidden X1 (k3_tarski X2) -> False)
  -> (forall X3 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X3 X2 -> False) -> (r2_hidden X1 (esk16_1 X2) -> False) -> r2_hidden X4 X1 -> r2_hidden X3 X4 -> r2_hidden X1 (k3_tarski (k3_tarski X2)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> (r2_hidden (esk8_2 X1 X2) (esk9_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk17_2 X1 X2) (esk18_2 X1 X2) -> False) -> r2_hidden X2 (esk16_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk14_2 X1 X2) (esk15_2 X1 X2) -> False) -> r2_hidden X2 (esk12_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk13_2 X1 X2) (esk14_2 X1 X2) -> False) -> r2_hidden X2 (esk12_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> r2_hidden X2 (esk20_1 X1) -> r1_xboole_0 (esk21_2 X1 X2) X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> r2_hidden X2 (esk16_1 X1) -> r1_xboole_0 (esk17_2 X1 X2) X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> r2_hidden X2 (esk12_1 X1) -> r1_xboole_0 (esk13_2 X1 X2) X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski (k3_tarski (k3_tarski X2))) -> False) -> r2_hidden X1 (esk20_1 X2) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X3 X2 X1, (r1_xboole_0 X1 (k2_xboole_0 X2 X3) -> False) -> r1_xboole_0 X1 X3 -> r1_xboole_0 X1 X2 -> False)
  -> (forall X3 X1 X2, (r1_xboole_0 X1 X2 -> False) -> r1_xboole_0 X1 (k2_xboole_0 X2 X3) -> False)
  -> (forall X3 X1 X2, (r1_xboole_0 X1 X2 -> False) -> r1_xboole_0 X1 (k2_xboole_0 X3 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk21_2 X1 X2) X2 -> False) -> r2_hidden X2 (esk20_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk18_2 X1 X2) X2 -> False) -> r2_hidden X2 (esk16_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk15_2 X1 X2) X2 -> False) -> r2_hidden X2 (esk12_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski (k3_tarski X2)) -> False) -> r2_hidden X1 (esk16_1 X2) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> r1_xboole_0 X1 X2 -> r2_hidden X1 (esk19_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski X2) -> False) -> r2_hidden X1 (esk12_1 X2) -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk23_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk23_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1, r2_hidden X1 esk1_0 -> r1_xboole_0 (esk2_1 X1) esk1_0 -> False)
  -> (forall X1, (r2_hidden (esk4_1 X1) (esk5_1 X1) -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X1, (r2_hidden (esk3_1 X1) (esk4_1 X1) -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X1, (r2_hidden (esk2_1 X1) (esk3_1 X1) -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (r2_hidden (esk5_1 X1) X1 -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r1_xboole_0 (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk22_1 X1) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k2_xboole_0 X1 X2) X3) = (k2_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((v1_xboole_0 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
let empty Un esk19_1 misses esk7_3 esk20_1 esk12_1 esk9_2 esk14_2 esk15_2 esk21_2 esk5_1 esk4_1 emptyset esk10_0 esk11_0 esk22_1 esk3_1 esk2_1 esk1_0 esk23_2 esk13_2 esk18_2 esk17_2 esk16_1 esk8_2 mem esk6_3 bun.
assume HC1 HC2 HC3 HC4 HC5 HC6 HC7 HC8 HC9 HC10 HC11 HC12 HC13 HC14 HC15 HC16 HC17 HC18 HC19 HC20 HC21 HC22 HC23 HC24 HC25 HC26 HC27 HC28 HC29 HC30 HC31 HC32 HC33 HC34 HC35 HC36 HC37 HC38 HC39 HC40 HC41 HC42 HC43 HC44 HC45 HC46 HC47 HC48 HC49 HC50 HC51 HC52 HC53 HC54 HC55 HC56 HC57 HC58.
claim LbunI1clause: forall X2 X4 X1 X3, (mem X1 X3 -> False) -> X3 = (bun X2 X4) -> mem X1 X2 -> False.
{ exact ??. }
claim LbunI2clause: forall X2 X4 X1 X3, (mem X1 X3 -> False) -> X3 = (bun X4 X2) -> mem X1 X2 -> False.
{ exact ??. }
claim LbunEclause: forall X3 X2 X1 X4, (mem X1 X4 -> False) -> (mem X1 X3 -> False) -> X2 = (bun X3 X4) -> mem X1 X2 -> False.
{ exact ??. }
claim L_bun_empty_clause: forall X2 X1, (empty X1 -> False) -> empty (bun X1 X2) -> False.
{ exact ??. }
claim LUnIclause: forall X3 X2 X1 X4, (mem X1 X4 -> False) -> X4 = (Un X3) -> mem X2 X3 -> mem X1 X2 -> False.
{ exact ??. }
set Z1skol := esk12_1.
claim LZ1clause1: forall X3 X5 X4 X1 X2, (empty X2 -> False) -> (misses X3 X2 -> False) -> (mem X1 (esk12_1 X2) -> False) -> mem X5 X1 -> mem X4 X5 -> mem X3 X4 -> mem X1 (Un X2) -> False.
{ exact ??. }
claim LZ1clause2: forall X2 X1, (empty X1 -> False) -> (mem (esk14_2 X1 X2) (esk15_2 X1 X2) -> False) -> mem X2 (esk12_1 X1) -> False.
{ exact ??. }
claim LZ1clause3: forall X2 X1, (empty X1 -> False) -> (mem (esk13_2 X1 X2) (esk14_2 X1 X2) -> False) -> mem X2 (esk12_1 X1) -> False.
{ exact ??. }
claim LZ1clause4: forall X2 X1, (empty X1 -> False) -> mem X2 (esk12_1 X1) -> misses (esk13_2 X1 X2) X1 -> False.
{ exact ??. }
claim LZ1clause5: forall X2 X1, (empty X1 -> False) -> (mem (esk15_2 X1 X2) X2 -> False) -> mem X2 (esk12_1 X1) -> False.
{ exact ??. }
claim LZ1clause6: forall X1 X2, (empty X2 -> False) -> (mem X1 (Un X2) -> False) -> mem X1 (esk12_1 X2) -> False.
{ exact ??. }
set Z2skol := esk16_1.
claim LZ2clause1: forall X3 X4 X1 X2, (empty X2 -> False) -> (misses X3 X2 -> False) -> (mem X1 (esk16_1 X2) -> False) -> mem X4 X1 -> mem X3 X4 -> mem X1 (Un (Un X2)) -> False.
{ exact ??. }
claim LZ2clause2: forall X2 X1, (empty X1 -> False) -> (mem (esk17_2 X1 X2) (esk18_2 X1 X2) -> False) -> mem X2 (esk16_1 X1) -> False.
{ exact ??. }
claim LZ2clause3: forall X2 X1, (empty X1 -> False) -> mem X2 (esk16_1 X1) -> misses (esk17_2 X1 X2) X1 -> False.
{ exact ??. }
claim LZ2clause4: forall X2 X1, (empty X1 -> False) -> (mem (esk18_2 X1 X2) X2 -> False) -> mem X2 (esk16_1 X1) -> False.
{ exact ??. }
claim LZ2clause5: forall X1 X2, (empty X2 -> False) -> (mem X1 (Un (Un X2)) -> False) -> mem X1 (esk16_1 X2) -> False.
{ exact ??. }
set Z3skol := esk20_1.
claim LZ3clause1: forall X3 X1 X2, (empty X2 -> False) -> (misses X3 X2 -> False) -> (mem X1 (esk20_1 X2) -> False) -> mem X3 X1 -> mem X1 (Un (Un (Un X2))) -> False.
{ exact ??. }
claim LZ3clause2: forall X2 X1, (empty X1 -> False) -> mem X2 (esk20_1 X1) -> misses (esk21_2 X1 X2) X1 -> False.
{ exact ??. }
claim LZ3clause3: forall X1 X2, (empty X2 -> False) -> (mem X1 (Un (Un (Un X2))) -> False) -> mem X1 (esk20_1 X2) -> False.
{ exact ??. }
claim LZ3clause4: forall X2 X1, (empty X1 -> False) -> (mem (esk21_2 X1 X2) X2 -> False) -> mem X2 (esk20_1 X1) -> False.
{ exact ??. }
set Z4skol := esk19_1.
claim LZ4clause1: forall X1 X2, (empty X2 -> False) -> (misses X1 X2 -> False) -> (mem X1 (esk19_1 X2) -> False) -> mem X1 (Un (Un (Un (Un X2)))) -> False.
{ exact ??. }
claim LZ4clause2: forall X1 X2, (empty X2 -> False) -> (mem X1 (Un (Un (Un (Un X2)))) -> False) -> mem X1 (esk19_1 X2) -> False.
{ exact ??. }
claim LZ4clause3: forall X1 X2, (empty X2 -> False) -> misses X1 X2 -> mem X1 (esk19_1 X2) -> False.
{ exact ??. }
claim LXne: empty esk1_0 -> False.
{ exact ??. }
set Yskol := esk22_1.
claim LY_clause1: forall X1, (empty X1 -> False) -> (mem (Yskol X1) X1 -> False) -> False.
{ exact ??. }
claim LY_clause2: forall X1, (empty X1 -> False) -> (misses (Yskol X1) X1 -> False) -> False.
{ exact ??. }
claim L_misses_bun_clause1: forall X3 X1 X2, (misses X1 X2 -> False) -> misses X1 (bun X2 X3) -> False.
{ exact ??. }
claim L_misses_bun_clause2: forall X3 X1 X2, (misses X1 X2 -> False) -> misses X1 (bun X3 X2) -> False.
{ exact ??. }
claim LmissesEclause: forall X2 X1 X3, mem X1 X3 -> mem X1 X2 -> misses X2 X3 -> False.
{ exact ??. }
claim L_cc_misses: forall X1, mem X1 esk1_0 -> misses (esk2_1 X1) esk1_0 -> False.
{ exact ??. }
claim L_cc_memX: forall X1, (mem (esk5_1 X1) X1 -> False) -> mem X1 esk1_0 -> False.
{ exact ??. }
claim L_cc_mem2: forall X1, (mem (esk4_1 X1) (esk5_1 X1) -> False) -> mem X1 esk1_0 -> False.
{ exact ??. }
claim L_cc_mem3: forall X1, (mem (esk3_1 X1) (esk4_1 X1) -> False) -> mem X1 esk1_0 -> False.
{ exact ??. }
claim L_cc_mem4: forall X1, (mem (esk2_1 X1) (esk3_1 X1) -> False) -> mem X1 esk1_0 -> False.
{ exact ??. }
claim LbunI1: forall X Y Z, mem Z X -> (mem Z (bun X Y) -> False) -> False.
{ let X Y Z.
  assume G1: mem Z X.
  assume G2: mem Z (bun X Y) -> False.
  exact LbunI1clause X Y Z (bun X Y) G2 (fun q H => H) G1.
}
claim LbunI2: forall X Y Z, mem Z Y -> (mem Z (bun X Y) -> False) -> False.
{ let X Y Z.
  assume G1: mem Z Y.
  assume G2: mem Z (bun X Y) -> False.
  exact LbunI2clause Y X Z (bun X Y) G2 (fun q H => H) G1.
}
claim LbunE: forall X Y Z, mem Z (bun X Y) -> (mem Z X -> False) -> (mem Z Y -> False) -> False.
{ let X Y Z.
  assume G1: mem Z (bun X Y).
  assume G2: mem Z X -> False.
  assume G3: mem Z Y -> False.
  exact LbunEclause X (bun X Y) Z Y G3 G2 (fun q H => H) G1.
}
claim LUnI: forall X Y Z, mem Z X -> mem Y Z -> (mem Y (Un X) -> False) -> False.
{ let X Y Z.
  assume G1 G2 G3.
  exact LUnIclause X Z Y (Un X) G3 (fun q H => H) G1 G2.
}
set X := esk1_0.
set Z1 := Z1skol X.
set Z2 := Z2skol X.
set Z3 := Z3skol X.
set Z4 := Z4skol X.
claim LZ1I: forall Y U V V2, mem Y (Un X) -> mem V2 Y -> mem V V2 -> mem U V -> (misses U X -> False) -> (mem Y Z1 -> False) -> False.
{ let Y U V V2.
  assume H1: mem Y (Un X).
  assume H2a: mem V2 Y.
  assume H2b: mem V V2.
  assume H3: mem U V.
  assume H4: misses U X -> False.
  assume H5: mem Y Z1 -> False.
  exact LZ1clause1 U V2 V Y X LXne ?? ?? ?? ?? ?? ??.
}
claim LZ1E: forall Y, mem Y Z1 -> (mem Y (Un X) -> forall u v v2, mem v2 Y -> mem v v2 -> mem u v -> (misses u X -> False) -> False) -> False.
{ let Y.
  assume H1: mem Y Z1.
  assume H2: mem Y (Un X) -> forall u v v2, mem v2 Y -> mem v v2 -> mem u v -> (misses u X -> False) -> False.
  apply (fun H: mem Y (Un X) -> False => LZ1clause6 Y X LXne H H1).
  assume H3: mem Y (Un X).
  apply (fun H: mem (esk15_2 X Y) Y -> False => LZ1clause5 Y X LXne H H1).
  assume H4: mem (esk15_2 X Y) Y.
  apply (fun H: mem (esk14_2 X Y) (esk15_2 X Y) -> False => LZ1clause2 Y X LXne H H1).
  assume H5: mem (esk14_2 X Y) (esk15_2 X Y).
  apply (fun H: mem (esk13_2 X Y) (esk14_2 X Y) -> False => LZ1clause3 Y X LXne H H1).
  assume H6: mem (esk13_2 X Y) (esk14_2 X Y).
  apply H2 H3 (esk13_2 X Y) (esk14_2 X Y) (esk15_2 X Y) H4 H5 H6.
  assume H7: misses (esk13_2 X Y) X.
  exact LZ1clause4 Y X LXne H1 H7.
}
claim LZ2I: forall Y U V, mem Y (Un (Un X)) -> mem V Y -> mem U V -> (misses U X -> False) -> (mem Y Z2 -> False) -> False.
{ let Y U V.
  assume H1: mem Y (Un (Un X)).
  assume H2: mem V Y.
  assume H3: mem U V.
  assume H4: misses U X -> False.
  assume H5: mem Y Z2 -> False.
  exact LZ2clause1 U V Y X LXne ?? ?? ?? ?? ??.
}
claim LZ2E: forall Y, mem Y Z2 -> (mem Y (Un (Un X)) -> forall u v, mem v Y -> mem u v -> (misses u X -> False) -> False) -> False.
{ let Y.
  assume H1: mem Y Z2.
  assume H2: mem Y (Un (Un X)) -> forall u v, mem v Y -> mem u v -> (misses u X -> False) -> False.
  apply (fun H: mem Y (Un (Un X)) -> False => LZ2clause5 Y X LXne H H1).
  assume H3: mem Y (Un (Un X)).
  apply (fun H: mem (esk18_2 X Y) Y -> False => LZ2clause4 Y X LXne H H1).
  assume H4: mem (esk18_2 X Y) Y.
  apply (fun H: mem (esk17_2 X Y) (esk18_2 X Y) -> False => LZ2clause2 Y X LXne H H1).
  assume H5: mem (esk17_2 X Y) (esk18_2 X Y).
  apply H2 H3 (esk17_2 X Y) (esk18_2 X Y) H4 H5.
  assume H6: misses (esk17_2 X Y) X.
  exact LZ2clause3 Y X LXne H1 H6.
}
claim LZ3I: forall Y y, mem Y (Un (Un (Un X))) -> mem y Y -> (misses y X -> False) -> (mem Y Z3 -> False) -> False.
{ let Y y.
  assume H1: mem Y (Un (Un (Un X))).
  assume H2: mem y Y.
  assume H3: misses y X -> False.
  assume H4: mem Y Z3 -> False.
  exact LZ3clause1 y Y X LXne H3 H4 H2 H1.
}
claim LZ3E: forall Y, mem Y Z3 -> (mem Y (Un (Un (Un X))) -> forall y, mem y Y -> (misses y X -> False) -> False) -> False.
{ let Y.
  assume H1: mem Y Z3.
  assume H2: mem Y (Un (Un (Un X))) -> forall y, mem y Y -> (misses y X -> False) -> False.
  apply (fun H: mem Y (Un (Un (Un X))) -> False => LZ3clause3 Y X LXne H H1).
  assume H3: mem Y (Un (Un (Un X))).
  apply (fun H: mem (esk21_2 X Y) Y -> False => LZ3clause4 Y X LXne H H1).
  assume H4: mem (esk21_2 X Y) Y.
  apply H2 H3 (esk21_2 X Y) H4.
  assume H5: misses (esk21_2 X Y) X.
  exact LZ3clause2 Y X LXne H1 H5.
}
claim LZ4I: forall Y, mem Y (Un (Un (Un (Un X)))) -> (misses Y X -> False) -> (mem Y Z4 -> False) -> False.
{ let Y.
  assume H1: mem Y (Un (Un (Un (Un X)))).
  assume H2: misses Y X -> False.
  assume H3: mem Y Z4 -> False.
  exact LZ4clause1 Y X LXne H2 H3 H1.
}
claim LZ4E: forall Y, mem Y Z4 -> (mem Y (Un (Un (Un (Un X)))) -> (misses Y X -> False) -> False) -> False.
{ let Y.
  assume H1: mem Y Z4.
  assume H2: mem Y (Un (Un (Un (Un X)))) -> (misses Y X -> False) -> False.
  apply (fun H:mem Y (Un (Un (Un (Un X)))) -> False => LZ4clause2 Y X LXne H H1).
  assume H3: mem Y (Un (Un (Un (Un X)))).
  apply H2 H3.
  assume H4: misses Y X.
  exact LZ4clause3 Y X LXne H4 H1.
}
set W := bun (bun (bun (bun X Z1) Z2) Z3) Z4.
set Y := Yskol W.
claim LW: empty W -> False.
{ assume H1: empty (bun (bun (bun (bun X Z1) Z2) Z3) Z4).
  apply (fun H: empty (bun (bun (bun X Z1) Z2) Z3) -> False => L_bun_empty_clause Z4 (bun (bun (bun X Z1) Z2) Z3) H H1).
  assume H2: empty (bun (bun (bun X Z1) Z2) Z3).
  apply (fun H: empty (bun (bun X Z1) Z2) -> False => L_bun_empty_clause Z3 (bun (bun X Z1) Z2) H H2).
  assume H3: empty (bun (bun X Z1) Z2).
  apply (fun H: empty (bun X Z1) -> False => L_bun_empty_clause Z2 (bun X Z1) H H3).
  assume H4: empty (bun X Z1).
  exact L_bun_empty_clause Z1 X LXne H4.
}
apply LY_clause1 W LW.
assume HYW1: mem Y W.
apply LY_clause2 W LW.
assume HYW2: misses Y W.
apply (fun H:misses Y (bun (bun (bun X Z1) Z2) Z3) -> False => L_misses_bun_clause1 Z4 Y (bun (bun (bun X Z1) Z2) Z3) H HYW2).
assume HYXZ1Z2Z3: misses Y (bun (bun (bun X Z1) Z2) Z3).
apply (fun H:misses Y (bun (bun X Z1) Z2) -> False => L_misses_bun_clause1 Z3 Y (bun (bun X Z1) Z2) H HYXZ1Z2Z3).
assume HYXZ1Z2: misses Y (bun (bun X Z1) Z2).
apply (fun H:misses Y (bun X Z1) -> False => L_misses_bun_clause1 Z2 Y (bun X Z1) H HYXZ1Z2).
assume HYXZ1: misses Y (bun X Z1).
apply (fun H:misses Y X -> False => L_misses_bun_clause1 Z1 Y X H HYXZ1).
assume HYX: misses Y X.
apply (fun H:misses Y Z1 -> False => L_misses_bun_clause2 X Y Z1 H HYXZ1).
assume HYZ1: misses Y Z1.
apply (fun H:misses Y Z2 -> False => L_misses_bun_clause2 (bun X Z1) Y Z2 H HYXZ1Z2).
assume HYZ2: misses Y Z2.
apply (fun H:misses Y Z3 -> False => L_misses_bun_clause2 (bun (bun X Z1) Z2) Y Z3 H HYXZ1Z2Z3).
assume HYZ3: misses Y Z3.
apply (fun H:misses Y Z4 -> False => L_misses_bun_clause2 (bun (bun (bun X Z1) Z2) Z3) Y Z4 H HYW2).
assume HYZ4: misses Y Z4.
claim L123: mem Y (bun (bun (bun X Z1) Z2) Z3) -> False.
{ assume H0: mem Y (bun (bun (bun X Z1) Z2) Z3).
  apply LbunE (bun (bun X Z1) Z2) Z3 Y H0.
  - assume H1: mem Y (bun (bun X Z1) Z2).
    apply LbunE (bun X Z1) Z2 Y H1.
    + assume H1: mem Y (bun X Z1).
      apply LbunE X Z1 Y H1.
      * assume H1: mem Y X.
        apply (fun H:mem (esk5_1 Y) Y -> False => L_cc_memX Y H H1).
        assume H2: mem (esk5_1 Y) Y.
        apply (fun H:mem (esk4_1 Y) (esk5_1 Y) -> False => L_cc_mem2 Y H H1).
        assume H3: mem (esk4_1 Y) (esk5_1 Y).
        apply (fun H:mem (esk3_1 Y) (esk4_1 Y) -> False => L_cc_mem3 Y H H1).
        assume H4: mem (esk3_1 Y) (esk4_1 Y).
        apply (fun H:mem (esk2_1 Y) (esk3_1 Y) -> False => L_cc_mem4 Y H H1).
        assume H5: mem (esk2_1 Y) (esk3_1 Y).
        apply LUnI X (esk5_1 Y) Y H1 H2.
        assume H6: mem (esk5_1 Y) (Un X).
        apply LZ1I (esk5_1 Y) (esk2_1 Y) (esk3_1 Y) (esk4_1 Y) H6 H3 H4 H5 (L_cc_misses Y H1).
        assume H7: mem (esk5_1 Y) Z1.
        exact LmissesEclause Y (esk5_1 Y) Z1 H7 H2 HYZ1.
      * assume H1: mem Y Z1.
        apply LZ1E Y H1.
        assume H2: mem Y (Un X).
        let u v v2.
        assume Hv2: mem v2 Y.
        assume Hv: mem v v2.
        assume Hu: mem u v.
        assume H3: misses u X -> False.
        apply LUnI (Un X) v2 Y H2 Hv2.
        assume H4: mem v2 (Un (Un X)).
        apply LZ2I v2 u v H4 Hv Hu H3.
        assume H5: mem v2 Z2.
        exact LmissesEclause Y v2 Z2 H5 Hv2 HYZ2.
    + assume H1: mem Y Z2.
      apply LZ2E Y H1.
      assume H2: mem Y (Un (Un X)).
      let u v.
      assume Hv: mem v Y.
      assume Hu: mem u v.
      assume H3: misses u X -> False.
      apply LUnI (Un (Un X)) v Y H2 Hv.
      assume H4: mem v (Un (Un (Un X))).
      apply LZ3I v u H4 Hu H3.
      assume H5: mem v Z3.
      exact LmissesEclause Y v Z3 H5 Hv HYZ3.
  - assume H1: mem Y Z3.
    apply LZ3E Y H1.
    assume HY: mem Y (Un (Un (Un X))).
    let y.
    assume Hy: mem y Y.
    assume H2: misses y X -> False.
    apply LUnI (Un (Un (Un X))) y Y HY Hy.
    assume H3: mem y (Un (Un (Un (Un X)))).
    apply LZ4I y H3 H2.
    assume H4: mem y Z4.
    exact LmissesEclause Y y Z4 H4 Hy HYZ4.
}
apply LbunE (bun (bun (bun X Z1) Z2) Z3) Z4 Y HYW1.
- exact L123.
- assume H1: mem Y Z4.
  apply LZ4E Y H1.
  assume H2: mem Y (Un (Un (Un (Un X)))).
  assume H3: misses Y X -> False.
  exact H3 HYX.
Qed.

