Theorem t3_xregular:
 forall k3_tarski:set -> set,
 forall esk6_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk10_1:set -> set,
 forall esk11_2:set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk12_1:set -> set,
 forall esk14_2:set -> set -> set,
 forall esk1_0:set,
 forall esk2_1:set -> set,
 forall esk13_1:set -> set,
 forall esk9_0:set,
 forall esk8_0:set,
 forall k1_xboole_0:set,
 forall esk3_1:set -> set,
 forall esk7_2:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk4_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk4_3 X1 X2 X3) X3 -> r2_hidden (esk4_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk4_3 X1 X2 X3) X3 -> r2_hidden (esk4_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk6_2 X1 X2) X3 -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk5_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r2_hidden (esk6_2 X1 X2) (esk7_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> r2_hidden X2 (esk10_1 X1) -> r1_xboole_0 (esk11_2 X1 X2) X1 -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X3 X2 -> False) -> (r2_hidden X1 (esk10_1 X2) -> False) -> r2_hidden X3 X1 -> r2_hidden X1 (k3_tarski X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X1 X2 -> False) -> (r2_hidden X1 (esk12_1 X2) -> False) -> r2_hidden X1 (k3_tarski (k3_tarski X2)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X3 X2 X1, (r1_xboole_0 X1 (k2_xboole_0 X2 X3) -> False) -> r1_xboole_0 X1 X3 -> r1_xboole_0 X1 X2 -> False)
  -> (forall X3 X1 X2, (r1_xboole_0 X1 X2 -> False) -> r1_xboole_0 X1 (k2_xboole_0 X2 X3) -> False)
  -> (forall X3 X1 X2, (r1_xboole_0 X1 X2 -> False) -> r1_xboole_0 X1 (k2_xboole_0 X3 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> r2_hidden X2 (esk10_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski (k3_tarski X2)) -> False) -> r2_hidden X1 (esk12_1 X2) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> r1_xboole_0 X1 X2 -> r2_hidden X1 (esk12_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski X2) -> False) -> r2_hidden X1 (esk10_1 X2) -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk14_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1, r2_hidden X1 esk1_0 -> r1_xboole_0 (esk2_1 X1) esk1_0 -> False)
  -> (forall X1, (r2_hidden (esk2_1 X1) (esk3_1 X1) -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (r2_hidden (esk3_1 X1) X1 -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r1_xboole_0 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk13_1 X1) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k2_xboole_0 X1 X2) X3) = (k2_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((v1_xboole_0 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
let Un esk6_2 empty esk10_1 esk11_2 misses esk12_1 esk14_2 esk1_0 esk2_1 esk13_1 esk9_0 esk8_0 emptyset esk3_1 esk7_2 esk5_3 mem esk4_3 bun.
assume H1: forall X1 X3 X2, (X3 = (bun X1 X2) -> False) -> mem (esk4_3 X1 X2 X3) X3 -> mem (esk4_3 X1 X2 X3) X1 -> False.
assume H2: forall X2 X3 X1, (X3 = (bun X1 X2) -> False) -> mem (esk4_3 X1 X2 X3) X3 -> mem (esk4_3 X1 X2 X3) X2 -> False.
assume H3: forall X1 X3 X2, (X3 = (bun X1 X2) -> False) -> (mem (esk4_3 X1 X2 X3) X3 -> False) -> (mem (esk4_3 X1 X2 X3) X2 -> False) -> (mem (esk4_3 X1 X2 X3) X1 -> False) -> False.
assume H4: forall X3 X2 X1, (X2 = (Un X1) -> False) -> mem X3 X1 -> mem (esk6_2 X1 X2) X3 -> mem (esk6_2 X1 X2) X2 -> False.
assume H5: forall X1 X2 X3, (mem (esk5_3 X1 X2 X3) X1 -> False) -> X2 = (Un X1) -> mem X3 X2 -> False.
assume H6: forall X2 X3 X1, (mem X1 (esk5_3 X2 X3 X1) -> False) -> X3 = (Un X2) -> mem X1 X3 -> False.
assume H7: forall X1 X2, (X2 = (Un X1) -> False) -> (mem (esk6_2 X1 X2) X2 -> False) -> (mem (esk6_2 X1 X2) (esk7_2 X1 X2) -> False) -> False.
assume H8: forall X2 X1, (empty X1 -> False) -> mem X2 (esk10_1 X1) -> misses (esk11_2 X1 X2) X1 -> False.
assume H9: forall X3 X1 X2, (empty X2 -> False) -> (misses X3 X2 -> False) -> (mem X1 (esk10_1 X2) -> False) -> mem X3 X1 -> mem X1 (Un X2) -> False.
assume H10: forall X1 X2, (empty X2 -> False) -> (misses X1 X2 -> False) -> (mem X1 (esk12_1 X2) -> False) -> mem X1 (Un (Un X2)) -> False.
assume H11: forall X1 X2, (X2 = (Un X1) -> False) -> (mem (esk6_2 X1 X2) X2 -> False) -> (mem (esk7_2 X1 X2) X1 -> False) -> False.
assume H12: forall X3 X2 X1, (misses X1 (bun X2 X3) -> False) -> misses X1 X3 -> misses X1 X2 -> False.
assume H13: forall X3 X1 X2, (misses X1 X2 -> False) -> misses X1 (bun X2 X3) -> False.
assume H14: forall X3 X1 X2, (misses X1 X2 -> False) -> misses X1 (bun X3 X2) -> False.
assume H15: forall X2 X1, (empty X1 -> False) -> (mem (esk11_2 X1 X2) X2 -> False) -> mem X2 (esk10_1 X1) -> False.
assume H16: forall X3 X2 X1 X4, (mem X1 X4 -> False) -> (mem X1 X3 -> False) -> X2 = (bun X3 X4) -> mem X1 X2 -> False.
assume H17: forall X1 X2, (empty X2 -> False) -> (mem X1 (Un (Un X2)) -> False) -> mem X1 (esk12_1 X2) -> False.
assume H18: forall X3 X2 X1 X4, (mem X1 X4 -> False) -> X4 = (Un X3) -> mem X2 X3 -> mem X1 X2 -> False.
assume H19: forall X2 X1 X3, mem X1 X3 -> mem X1 X2 -> misses X2 X3 -> False.
assume H20: forall X2 X4 X1 X3, (mem X1 X3 -> False) -> X3 = (bun X2 X4) -> mem X1 X2 -> False.
assume H21: forall X2 X4 X1 X3, (mem X1 X3 -> False) -> X3 = (bun X4 X2) -> mem X1 X2 -> False.
assume H22: forall X1 X2, (empty X2 -> False) -> misses X1 X2 -> mem X1 (esk12_1 X2) -> False.
assume H23: forall X1 X2, (empty X2 -> False) -> (mem X1 (Un X2) -> False) -> mem X1 (esk10_1 X2) -> False.
assume H24: forall X1 X2, (misses X1 X2 -> False) -> (mem (esk14_2 X1 X2) X1 -> False) -> False.
assume H25: forall X2 X1, (misses X1 X2 -> False) -> (mem (esk14_2 X1 X2) X2 -> False) -> False.
assume H26: forall X2 X1, (empty X1 -> False) -> empty (bun X1 X2) -> False.
assume H27: forall X2 X1, (empty X1 -> False) -> empty (bun X2 X1) -> False.
assume H28: forall X1, mem X1 esk1_0 -> misses (esk2_1 X1) esk1_0 -> False.
assume H29: forall X1, (mem (esk2_1 X1) (esk3_1 X1) -> False) -> mem X1 esk1_0 -> False.
assume H30: forall X2 X1, mem X2 X1 -> mem X1 X2 -> False.
assume H31: forall X1, (mem (esk3_1 X1) X1 -> False) -> mem X1 esk1_0 -> False.
assume H32: forall X2 X1, (misses X2 X1 -> False) -> misses X1 X2 -> False.
assume H33: forall X1 X2, empty X2 -> mem X1 X2 -> False.
assume H34: forall X1, (empty X1 -> False) -> (misses (esk13_1 X1) X1 -> False) -> False.
assume H35: forall X1, (empty X1 -> False) -> (mem (esk13_1 X1) X1 -> False) -> False.
assume H36: forall X2 X1, (X1 = X2 -> False) -> empty X2 -> empty X1 -> False.
assume H37: forall X1, (X1 = emptyset -> False) -> empty X1 -> False.
assume H38: empty esk9_0 -> False.
assume H39: empty esk1_0 -> False.
assume H40: forall X2 X3 X1, ((bun (bun X1 X2) X3) = (bun X1 (bun X2 X3)) -> False) -> False.
assume H41: forall X2 X1, ((bun X1 X2) = (bun X2 X1) -> False) -> False.
assume H42: forall X1, ((bun X1 X1) = X1 -> False) -> False.
assume H43: forall X1, ((bun X1 emptyset) = X1 -> False) -> False.
assume H44: (empty esk8_0 -> False) -> False. (** wlog: esk8_0 = emptyset and can throw this away **)
assume H45: (empty emptyset -> False) -> False.
set X := esk1_0.
set Z1 := esk10_1 X.
set Z2 := esk12_1 X.
claim LZ1I: forall Y y, mem Y (Un X) -> mem y Y -> (misses y X -> False) -> (mem Y Z1 -> False) -> False.
{ let Y y.
  assume H46: mem Y (Un X).
  assume H47: mem y Y.
  assume H48: misses y X -> False.
  assume H49: mem Y Z1 -> False.
  exact H9 y Y X H39 H48 H49 H47 H46.
}
claim LZ1E: forall Y, mem Y Z1 -> (mem Y (Un X) -> forall y, mem y Y -> (misses y X -> False) -> False) -> False.
{ let Y.
  assume H46: mem Y Z1.
  assume H47: mem Y (Un X) -> forall y, mem y Y -> (misses y X -> False) -> False.
  apply (fun H: mem Y (Un X) -> False => H23 Y X H39 H H46).
  assume H48: mem Y (Un X).
  apply (fun H: mem (esk11_2 X Y) Y -> False => H15 Y X H39 H H46).
  assume H49: mem (esk11_2 X Y) Y.
  apply H47 H48 (esk11_2 X Y) H49.
  assume H50: misses (esk11_2 X Y) X.
  exact H8 Y X H39 H46 H50.
}
claim LZ2I: forall Y, mem Y (Un (Un X)) -> (misses Y X -> False) -> (mem Y Z2 -> False) -> False.
{ let Y.
  assume H46: mem Y (Un (Un X)).
  assume H47: misses Y X -> False.
  assume H48: mem Y Z2 -> False.
  exact H10 Y X H39 H47 H48 H46.
}
claim LZ2E: forall Y, mem Y Z2 -> (mem Y (Un (Un X)) -> (misses Y X -> False) -> False) -> False.
{ let Y.
  assume H46: mem Y Z2.
  assume H47: mem Y (Un (Un X)) -> (misses Y X -> False) -> False.
  apply (fun H:mem Y (Un (Un X)) -> False => H17 Y X H39 H H46).
  assume H48: mem Y (Un (Un X)).
  apply H47 H48.
  assume H49: misses Y X.
  exact H22 Y X H39 H49 H46.
}
set W := bun (bun X Z1) Z2.
set Y := esk13_1 W.
claim LW: empty W -> False.
{ assume H46: empty (bun (bun X Z1) Z2).
  apply (fun H: empty (bun X Z1) -> False => H26 Z2 (bun X Z1) H H46).
  assume H47: empty (bun X Z1).
  exact H26 Z1 X H39 H47.
}
apply H35 W LW.
assume HYW1: mem Y W.
apply H34 W LW.
assume HYW2: misses Y W.
apply (fun H:misses Y (bun X Z1) -> False => H13 Z2 Y (bun X Z1) H HYW2).
assume HYXZ1: misses Y (bun X Z1).
apply (fun H:misses Y X -> False => H13 Z1 Y X H HYXZ1).
assume HYX: misses Y X.
apply (fun H:misses Y Z1 -> False => H14 X Y Z1 H HYXZ1).
assume HYZ1: misses Y Z1.
apply (fun H:misses Y Z2 -> False => H14 (bun X Z1) Y Z2 H HYW2).
assume HYZ2: misses Y Z2.
apply H16 (bun X Z1) W Y Z2.
- assume H46: mem Y Z2.
  apply LZ2E Y H46.
  assume H47: mem Y (Un (Un X)).
  assume H48: misses Y X -> False.
  exact H48 HYX.
- assume H46: mem Y (bun X Z1).
  apply H16 X (bun X Z1) Y Z1.
  + assume H46: mem Y Z1.
    apply LZ1E Y H46.
    assume H47: mem Y (Un X).
    let y.
    assume H48: mem y Y.
    assume H49: misses y X -> False.
    apply (fun H:mem y (Un (Un X)) -> False => H18 (Un X) Y y (Un (Un X)) H (fun q H => H) H47 H48).
    assume H50: mem y (Un (Un X)).
    apply LZ2I y H50 H49.
    assume H51: mem y Z2.
    exact H19 Y y Z2 H51 H48 HYZ2.
  + assume H46: mem Y X.
    apply (fun H:mem (esk3_1 Y) Y -> False => H31 Y H H46).
    assume H47: mem (esk3_1 Y) Y.
    apply (fun H:mem (esk2_1 Y) (esk3_1 Y) -> False => H29 Y H H46).
    assume H48: mem (esk2_1 Y) (esk3_1 Y).
    apply (fun H:mem (esk3_1 Y) (Un X) -> False => H18 X Y (esk3_1 Y) (Un X) H (fun q H => H) H46 H47).
    assume H49: mem (esk3_1 Y) (Un X).
    apply LZ1I (esk3_1 Y) (esk2_1 Y) H49 H48 (H28 Y H46).
    assume H50: mem (esk3_1 Y) Z1.
    exact H19 Y (esk3_1 Y) Z1 H50 H47 HYZ1.
  + reflexivity.
  + exact H46.
- reflexivity.
- exact HYW1.
Qed.

