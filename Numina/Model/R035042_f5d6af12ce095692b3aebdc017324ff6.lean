import Mathlib

theorem number_theory_75106 (N : ℕ) (hN : N % 2020 = 0) (hN' : (Nat.digits 10 N).length = 6)
    (hN'' : ∀ i j, i ≠ j → ¬(2020 ∣ Nat.ofDigits 10 (List.map (fun k => if k = i then j else if k = j then i else k) (Nat.digits 10 N))))
    (hN''' : (Nat.digits 10 N).toFinset.card = 6) :
    (Nat.digits 10 N).length = 6 := by 
  exact hN'