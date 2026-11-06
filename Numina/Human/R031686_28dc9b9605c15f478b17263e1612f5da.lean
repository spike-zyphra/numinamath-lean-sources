import Mathlib
open Real

/- Let $a, b$, and $c$ be non-zero real numbers and let $a \geq b \geq c$. Prove the inequality
$$
\frac{a^{3}-c^{3}}{3} \geq a b c\left(\frac{a-b}{c}+\frac{b-c}{a}\right)
$$
When does equality hold? -/
theorem inequalities_607925 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
(hord : a ≥ b ∧ b ≥ c) : (a^3 - c^3) / 3 ≥ a * b * c * ((a - b) / c + (b - c) / a)
∧ ((a^3 - c^3) / 3 = a * b * c * ((a - b) / c + (b - c) / a) ↔ a = c) := by 
  -- Since $c-b \leq 0 \leq a-b$, we have $(a-b)^{3} \geq(c-b)^{3}$,
  have ha_sub_b_nonneg: a - b ≥ 0 := by linarith
  have ha_sub_b_cube_nonneg: (a - b) ^ 3 ≥ 0 := by simp [ha_sub_b_nonneg]
  have hc_sub_b_nonpos: c - b ≤ 0 := by linarith
  have hc_sub_b_cube_nonpos: (c - b) ^ 3 ≤ 0 := by exact Odd.pow_nonpos (Nat.odd_iff.mpr rfl) hc_sub_b_nonpos
  -- or $ a^{3}-3 a^{2} b+3 a b^{2}-b^{3} \geq c^{3}-3 b c^{2}+3 b^{2} c-b^{3} $
  have h1: a ^ 3 - 3 * a ^ 2 * b + 3 * a * b ^ 2 - b ^ 3 ≥ c ^ 3 - 3 * b * c ^ 2 + 3 * b ^ 2 * c - b ^ 3:= by
    calc
      _ = (a - b) ^ 3 := by ring_nf
      _ ≥ (c - b) ^ 3 := by linarith
      _ = c ^ 3 - 3 * b * c ^ 2 + 3 * b ^ 2 * c - b ^ 3 := by ring_nf
  -- On simplifying this, we immediately have the desired result.
  have h2: a ^ 3 - c ^ 3 ≥ 3 * (a ^ 2 * b - a * b ^ 2 + b ^ 2 * c - b * c ^ 2) := by linarith
  have h3: a * b * c * ((a - b) / c + (b - c) / a) = a ^ 2 * b - a * b ^ 2 + b ^ 2 * c - b * c ^ 2 := by 
    calc
      _ = a * b * c * (a - b)/c + a * b * c * (b - c)/a := by ring_nf
      _ = a * b * (a - b) + b * c * (b - c) := by field_simp; ring_nf
      _ = a ^ 2 * b - a * b ^ 2 + b ^ 2 * c - b * c ^ 2 := by ring_nf
  rw [← h3] at h2
  constructor
  linarith
  have hc_le_a : c ≤ a := by linarith
  -- As for equality, it holds only when $a = c$.
  constructor
  cases gt_or_eq_of_le hc_le_a with
  | inl hc_lt_a =>
    -- If $a>c$, then $(a-b)^{3}>(c-b)^{3}$, which makes the proved inequality a strict one. 
    intro h
    by_contra hcon
    have h4: (c - b) < 0 ∨ 0 < (a - b) := by 
      by_contra heq
      push_neg at heq
      simp at heq
      have : ¬ (c < a) := by linarith
      contradiction
    have h5: (c - b) ^ 3 < (a - b) ^ 3 := by 
      cases h4 with
      | inl h4_left => 
        linarith [Odd.pow_neg (Nat.odd_iff.mpr (show 3 % 2 = 1 by rfl)) h4_left]
      | inr h4_right => 
        have : 0 < (a - b) ^ 3 := by simp [h4_right]
        linarith
    have h1_str: a ^ 3 - 3 * a ^ 2 * b + 3 * a * b ^ 2 - b ^ 3 > c ^ 3 - 3 * b * c ^ 2 + 3 * b ^ 2 * c - b ^ 3:= by
      calc
        _ = (a - b) ^ 3 := by ring_nf
        _ > (c - b) ^ 3 := by linarith
        _ = c ^ 3 - 3 * b * c ^ 2 + 3 * b ^ 2 * c - b ^ 3 := by ring_nf
    have h2_str: a ^ 3 - c ^ 3 > 3 * (a ^ 2 * b - a * b ^ 2 + b ^ 2 * c - b * c ^ 2) := by linarith
    rw [← h3] at h2_str
    linarith
  | inr hc_eq_a => 
    -- If $a=c$, the result is obivious.
    rw [hc_eq_a]; simp
  -- So $a=c$ is a necessary condition for equality.
  -- A sufficient condition for equality is $a=c$. 
  intro hc_eq_a
  rw [hc_eq_a]
  simp; right
  field_simp