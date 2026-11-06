import Mathlib

theorem number_theory_323688 :
    (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 3 ∣ x}) * 5 > (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 4 ∣ x}) * 6 ∧
    (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 5 ∣ x}) * 3 > (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 6 ∣ x}) * 2 := by 
  have h1 : Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 3 ∣ x} = 33 := by
    have h_eq1 : {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 3 ∣ x} = 
      Finset.filter (fun (x : ℕ) => 3 ∣ x) (Finset.Icc 1 101) := by 
      ext x
      simp 
    rw [h_eq1]
    rw [Nat.card_eq_fintype_card]
    have : (Finset.filter (fun (x : ℕ) => 3 ∣ x) (Finset.Icc 1 101)).card = 33 := by
      native_decide 
    exact_mod_cast this 
  have h2 : Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 4 ∣ x} = 25 := by 
    have eq53 : {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 4 ∣ x} = Finset.filter (fun (x : ℕ) => 4 ∣ x) (Finset.Icc 1 101) := by
      ext x
      simp 
    rw [eq53] 
    rw [Nat.card_eq_fintype_card]
    have : (Finset.filter (fun (x : ℕ) => 4 ∣ x) (Finset.Icc 1 101)).card = 25 := by
      native_decide
    exact_mod_cast this 
  have h3 : Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 5 ∣ x} = 20 := by 
    have h_eq3 : {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 5 ∣ x} = Finset.filter (fun (x : ℕ) => 5 ∣ x) (Finset.Icc 1 101) := by 
      ext x 
      simp 
    rw [h_eq3] 
    rw [Nat.card_eq_fintype_card]
    have : (Finset.filter (fun (x : ℕ) => 5 ∣ x) (Finset.Icc 1 101)).card = 20 := by
      native_decide 
    exact_mod_cast this 
  have h4 : Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 6 ∣ x} = 16 := by 
    have h_eq4 : {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 6 ∣ x} = Finset.filter (fun (x : ℕ) => 6 ∣ x) (Finset.Icc 1 101) := by 
      ext x 
      simp 
    rw [h_eq4] 
    rw [Nat.card_eq_fintype_card]
    have : (Finset.filter (fun (x : ℕ) => 6 ∣ x) (Finset.Icc 1 101)).card = 16 := by
      native_decide 
    exact_mod_cast this 
  constructor 
  · -- Show (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 3 ∣ x}) * 5 > (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 4 ∣ x}) * 6 
    calc 
      (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 3 ∣ x}) * 5 = 33 * 5 := by rw [h1]
      _ > 25 * 6 := by norm_num 
      _ = (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 4 ∣ x}) * 6 := by rw [h2]
  · -- Show (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 5 ∣ x}) * 3 > (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 6 ∣ x}) * 2 
    calc 
      (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 5 ∣ x}) * 3 = 20 * 3 := by rw [h3]
      _ > 16 * 2 := by norm_num 
      _ = (Nat.card {x : ℕ | x ∈ Finset.Icc 1 101 ∧ 6 ∣ x}) * 2 := by rw [h4]