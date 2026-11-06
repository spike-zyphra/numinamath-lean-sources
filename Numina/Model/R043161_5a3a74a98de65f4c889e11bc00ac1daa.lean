import Mathlib

theorem inequalities_109791 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hord : a ≥ b ∧ b ≥ c) :
    (a^3 - c^3)/3 ≥ a * b * c * ((a - b)/c + (b - c)/a) := by
  have h1 : a ≥ b := hord.1
  have h2 : b ≥ c := hord.2
  have h3 : a ≥ c := by linarith
  have h4 : a - b ≥ 0 := by linarith
  have h5 : b - c ≥ 0 := by linarith
  have h6 : a - c ≥ 0 := by linarith
  -- transform to clear denominators
  have eq1 : a * b * c * ((a - b)/c + (b - c)/a) = a * b * (a - b) + b * c * (b - c) := by
    field_simp [hc, ha]
    <;> ring
  rw [eq1] at *
  -- ineq is equivalent to
  -- $a^3 - c^3 \geq 3 \cdot (ab(a - b) + bc(b - c))$
  have h7 : a ^ 3 - c ^ 3 ≥ 3 * (a * b * (a - b) + b * c * (b - c)) := by
    -- to prove this ineq, we can show ineq equivalent to
    -- $ a^3 -c^3 - 3(ab(a-b)+bc(b-c)) ≥ 0 $
    have h71 : a^3 - c^3 - 3 * (a * b * (a - b) + b * c * (b - c)) ≥ 0 := by
      -- algebra to show
      -- $a^3 -c^3 - 3(ab(a-b)+bc(b-c)) = (a-b)^3+(b-c)^3\geq0 $.
      have h8 : a^3 - c^3 - 3 * (a * b * (a - b) + b * c * (b - c)) = (a - b)^3 + (b - c)^3 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
      rw [h8]
      have h6 : (a - b) ^ 3 ≥ 0 := by
        have h61 : (a - b) ≥ 0 := by linarith
        have h71 : (a - b) ^ 3 = (a - b) * (a - b) * (a - b) := by ring_nf
        rw [h71]
        apply mul_nonneg
        apply mul_nonneg
        all_goals try linarith
      have h7 : (b - c) ^ 3 ≥ 0 := by
        have h81 : (b - c) ≥ 0 := by linarith
        -- prove by factoring, using ring_nf to show product.
        have h91 : (b - c) ^ 3 = (b - c) * (b - c) * (b - c) := by ring_nf
        rw [h91]
        apply mul_nonneg
        apply mul_nonneg
        all_goals try linarith
      linarith
    linarith
  -- prove result by linarith
  linarith