import Mathlib

open Finset

theorem algebra_609769 :
    {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | |a| ≤ 5 ∧ |b| ≤ 5 ∧ |c| ≤ 5 ∧ |d| ≤ 5 ∧
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 = (a + b + c + d) * (a - b + c - d) * ((a - c) ^ 2 + (b - d) ^ 2)}.encard =
    49 := by
  have h1 : {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | |a| ≤ 5 ∧ |b| ≤ 5 ∧ |c| ≤ 5 ∧ |d| ≤ 5 ∧
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 = (a + b + c + d) * (a - b + c - d) * ((a - c) ^ 2 + (b - d) ^ 2)} = Finset.filter (fun s : ℤ × ℤ × ℤ × ℤ =>
      let (a, b, c, d) := s
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 = (a + b + c + d) * (a - b + c - d) * ((a - c) ^ 2 + (b - d) ^ 2) ) (Finset.Icc (-5 : ℤ) 5 ×ˢ Finset.Icc (-5 : ℤ) 5 ×ˢ Finset.Icc (-5 : ℤ) 5 ×ˢ Finset.Icc (-5 : ℤ) 5) := by
    ext ⟨a, b, c, d⟩
    simp
    <;> try { tauto }
    <;> try { 
      norm_num [abs_le]
      <;> try { 
        omega 
      } 
    }
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide