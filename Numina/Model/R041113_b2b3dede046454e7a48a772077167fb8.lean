import Mathlib

theorem algebra_315350 {a b c k : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : k = (2 * a + b) / c) (h2 : k = (2 * c + a) / b) (h3 : k = (2 * b + c) / a) :
    k = 3 := by

  have eq1 : k * c = 2 * a + b := by
    field_simp [hc] at h1 ⊢
    linarith
  have eq2 : k * b = 2 * c + a := by
    field_simp [hb] at h2 ⊢
    linarith
  have eq3 : k * a = 2 * b + c := by
    field_simp [ha] at h3 ⊢
    linarith
  have h4 : k * (a + b + c) = 3 * (a + b + c) := by
    calc
      k * (a + b + c) = k * a + k * b + k * c := by
        ring
      _ = (2 * b + c) + (2 * c + a) + (2 * a + b) := by
        rw [show k * a = 2 * b + c by linarith [eq3]]
        rw [show k * b = 2 * c + a by linarith [eq2]]
        rw [show k * c = 2 * a + b by linarith [eq1]]
      _ = 3 * (a + b + c) := by
        ring
  have h5 : (k - 3) * (a + b + c) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- Case k - 3 = 0, so k = 3
    linarith
  · -- Case a + b + c = 0
    have h0 : a + b + c = 0 := h7
    have ha' : a = -b - c := by linarith
    rw [show a = -b - c by linarith [h0]] at eq1 eq2 eq3
    -- Now we have three equations in b and c
    -- eq1: k * c = -b - 2 * c
    -- eq2: k * b = c - b
    -- eq3: k * (-b - c) = 2 * b + c
    -- From eq2: k * b + b = c
    -- So c = b * (k + 1)
    have sub1 : c = b * (k + 1) := by
      have eq2' : k * b = c - b := by
        linarith
      have : c = k * b + b := by
        linarith
      have : c = b * (k + 1) := by
        linarith
      assumption
    -- Substitute c = b * (k + 1) into eq1
    -- k * (b * (k + 1)) = -b - 2 * (b * (k + 1))
    rw [show c = b * (k + 1) by linarith [sub1]] at eq1
    -- From eq1: k * (b * (k + 1)) = -b - 2 * (b * (k + 1))
    -- So b * (k * (k + 1) + 2 * (k + 1) + 1) = 0
    -- Since hb: b ≠ 0, we have k * (k + 1) + 2 * (k + 1) + 1 = 0
    have eq1_sub : b * (k * (k + 1) + 2 * (k + 1) + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 eq1_sub) with h8 h9
    · -- Case b = 0
      exfalso
      apply hb
      linarith
    · -- Case k * (k + 1) + 2 * (k + 1) + 1 = 0
      -- This simplifies to k^2 + 3k + 3 = 0
      have h_eq : k^2 + 3 * k + 3 = 0 := by
        nlinarith
      -- This quadratic has discriminant 9 - 12 = -3
      -- Which is negative, so no real solutions
      -- This contradicts the fact that our variable k is real
      have h_discr : (k + 3 / 2) ^ 2 + 3 / 4 = 0 := by
        nlinarith
      have h_neg_sq : (k + 3 / 2) ^ 2 ≥ 0 := by
        apply sq_nonneg
      -- Since (k + 3/2)^2 ≥ 0, but (k + 3/2)^2 + 3/4 = 0
      -- We have that (k + 3/2)^2 = -3/4 < 0
      -- Which is impossible for a real number
      -- Lean's arithmetic reasoner should see the contradiction
      nlinarith
  all_goals try tauto
  all_goals try nlinarith
  <;> try { assumption <;> tauto }
  <;> try { trivial }
  <;> try { tauto }
  <;> try { trivial }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { aesop }
  <;> try { tauto }
  <;> try { nlinarith }
  all_goals try ring_nf <;> try { try { assumption } <;> try { tauto } } <;> try { nlinarith }
  <;> try { assumption <;> tauto }
  <;> try { nlinarith }