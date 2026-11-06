import Mathlib

open Finset

/- Find the number of quadruples $(a, b, c, d)$ of integers with absolute value at most 5 such that

$$
\left(a^{2}+b^{2}+c^{2}+d^{2}\right)^{2}=(a+b+c+d)(a-b+c-d)\left((a-c)^{2}+(b-d)^{2}\right)
$$ -/
theorem algebra_609769 :
    {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | |a| ≤ 5 ∧ |b| ≤ 5 ∧ |c| ≤ 5 ∧ |d| ≤ 5 ∧
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 = (a + b + c + d) * (a - b + c - d) * ((a - c) ^ 2 + (b - d) ^ 2)}.encard =
    49 := by
  -- It suffices to reduce the problem to a problem of Finset.
  suffices H : {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | |a| ≤ 5 ∧ |b| ≤ 5 ∧ |c| ≤ 5 ∧ |d| ≤ 5 ∧
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 = (a + b + c + d) * (a - b + c - d) * ((a - c) ^ 2 + (b - d) ^ 2)} =
    (Icc (-5) 5 ×ˢ Icc (-5) 5 ×ˢ Icc (-5) 5 ×ˢ Icc (-5) 5).filter (fun (a, b, c, d) =>
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 = (a + b + c + d) * (a - b + c - d) * ((a - c) ^ 2 + (b - d) ^ 2)) by
    -- So we can compute the cardinality by `native_decide`.
    rw [H, Set.encard_coe_eq_coe_finsetCard]
    native_decide
  -- The equivalence is obvious.
  ext ⟨a, b, c, d⟩
  simp [abs_le]
  tauto
