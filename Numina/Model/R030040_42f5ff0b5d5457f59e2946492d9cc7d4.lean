import Mathlib

def f (n : ℕ) := (Nat.digits 10 n).prod

theorem number_theory_223664 :
    {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 1}.encard = 1 ∧
    {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 625}.encard = 1 ∧
    {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 2401}.encard = 1 ∧
    {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 4096}.encard = 1 ∧
    {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 6561}.encard = 1 := by 
  have h1 : {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 1} = Finset.filter (fun n => (Nat.digits 10 n).prod = 1) (Finset.Icc 1000 9999) := by
    ext n
    simp [f]
  have h2 : {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 625} = Finset.filter (fun n => (Nat.digits 10 n).prod = 625) (Finset.Icc 1000 9999) := by
    ext n
    simp [f]
  have h3 : {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 2401} = Finset.filter (fun n => (Nat.digits 10 n).prod = 2401) (Finset.Icc 1000 9999) := by
    ext n
    simp [f]
  have h4 : {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 4096} = Finset.filter (fun n => (Nat.digits 10 n).prod = 4096) (Finset.Icc 1000 9999) := by
    ext n
    simp [f]
  have h5 : {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 6561} = Finset.filter (fun n => (Nat.digits 10 n).prod = 6561) (Finset.Icc 1000 9999) := by
    ext n
    simp [f]
  rw [h1, h2, h3, h4, h5]
  constructor
  · -- Show that {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 1} has cardinality 1
    rw [Set.encard_coe_eq_coe_finsetCard]
    native_decide
  constructor
  · -- Show that {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 625} has cardinality 1
    rw [Set.encard_coe_eq_coe_finsetCard]
    native_decide
  constructor
  · -- Show that {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 2401} has cardinality 1
    rw [Set.encard_coe_eq_coe_finsetCard]
    native_decide
  constructor
  · -- Show that {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 4096} has cardinality 1
    rw [Set.encard_coe_eq_coe_finsetCard]
    native_decide
  · -- Show that {n | n ∈ Finset.Icc 1000 9999 ∧ f n = 6561} has cardinality 1
    rw [Set.encard_coe_eq_coe_finsetCard]
    native_decide