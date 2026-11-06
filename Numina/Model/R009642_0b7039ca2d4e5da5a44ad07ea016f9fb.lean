import Mathlib

theorem number_theory_16786 : (((Finset.product (Finset.range 10) (Finset.range 10)).filter (fun (G, H) => 72 ∣ Nat.ofDigits 10 [6, H, 2, 7, 0, 5, G, 1, 4, 5])).image (fun (G, H) => G * H)).sum id = 59 := by
  native_decide