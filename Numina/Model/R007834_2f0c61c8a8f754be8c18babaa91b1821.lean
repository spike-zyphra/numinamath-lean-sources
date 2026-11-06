import Mathlib

theorem number_theory_19379 :
    (∑ x in (ZMod.fintype (2^4)).elems.filter (fun x => IsUnit x) , x.val) -
    (∑ x in (ZMod.fintype (2^4)).elems.filter (fun x => ¬IsUnit x), x.val) = 8 := by
  native_decide