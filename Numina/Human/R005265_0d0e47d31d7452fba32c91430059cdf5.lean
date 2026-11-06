import Mathlib

/- Trouver toutes les suites périodiques $\left(x_{n}\right)_{n \in \mathbb{N}^{*}}$ de réels strictement positifs, et telles que pour tout $\mathrm{n} \geqslant 1$,

$$
x_{n+2}=\frac{1}{2}\left(\frac{1}{x_{n+1}}+x_{n}\right) .
$$ -/
theorem algebra_607260 (x : ℕ → ℝ) (xpos : ∀ n, 0 < x n)
  (hx: ∃ c, 0 < c ∧ Function.Periodic x c):
  (∀n, x (n+2) = (1/2) * (1 / x (n+1) + x n) ) ↔
  (∃ (a:ℝ), 0 < a ∧ x = fun n => if Even n then a else 1/a) := by

  constructor
  · intro h
    -- from x_{n+2} = (1/x_{n+1} + x_n) / 2,
    -- we have x_{n+2} x_{n+1} - 1 = 1/2 (x_{n+1} x_n - 1)
    replace h: ∀n, x (n+2) * x (n+1) - 1 =
      1/2 * (x (n+1) * x n - 1) := by
      intro n
      specialize h n
      field_simp [(xpos (n+1)).ne'] at h
      linarith only [h]
    -- induction,  we find x_{n+2} x_{n+1} - 1 = 1/2^(n+1) (x_1 x_0 - 1)
    have h': ∀n, x (n+2) * x (n+1) - 1 = 1 / 2^(n+1) * (x 1 * x 0 - 1) := by
      intro n
      induction' n with n ih
      · specialize h 0
        simpa only [zero_add, pow_one, one_div] using h
      · rw [h (n+1), ih, ← mul_assoc]
        simp only [mul_eq_mul_right_iff]
        left; ring
    -- suppose x has periodic c.
    rcases hx with ⟨c, cpos, hc⟩
    -- then x_{n+1} x_n - 1 also has periodic c
    have hx': Function.Periodic (fun i => x (i+1) * x i - 1) c := by
      suffices Function.Periodic (fun i => x (i+1) * x i) c by
        exact fun x_1 => congrFun (congrArg HSub.hSub (this x_1)) 1
      apply Function.Periodic.mul ?_ ?_
      · exact Function.Periodic.add_const hc 1
      · exact hc
    -- then x1 x0 = 1, otherwise contradicts periodic c.
    have h1: x 1 * x 0 = 1 := by
      have hh1 := h' c
      have hh2 := h' (c+c)
      have hh3 := hx' (c+1)
      simp only at hh3
      rw [show c+1+c+1 = c+c+2 by ring, show c+1+c = c+c+1 by ring,
      show c+1+1 = c+2 by ring, hh1, hh2] at hh3
      simp only [one_div, mul_eq_mul_right_iff, inv_inj, Nat.ofNat_pos,
      ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, pow_right_inj₀,
      Nat.add_right_cancel_iff, Nat.add_eq_left, cpos.ne', false_or] at hh3
      linarith only [hh3]
    -- so x_{n+2} x_{n+1} = 1 for all n, the sequence is x0, 1/x0, x0, 1/x0, ...
    use x 0
    refine ⟨xpos 0, ?_⟩
    have: ∀ n, x n = if Even n then x 0 else 1 / x 0 := by
      intro n
      induction' n with n ih
      · simp
      · by_cases nz: n = 0
        · simp only [nz, zero_add, Nat.not_even_one, ↓reduceIte, one_div]
          field_simp [(xpos 0).ne']
          exact h1
        by_cases hhn: n = 1
        · specialize h 0
          simp only [zero_add, one_div, h1, sub_self, mul_zero] at h
          have h2: x 1 = 1 / x 0 := by
            rw [← h1]
            simp [(xpos 0).ne']
          have h3: x 2 = x 0 := by
            replace h: x 2 = 1 / x 1 := by
              field_simp [(xpos 1).ne']
              linarith only [h]
            simp [h, h2]
          simp [hhn, h3]
        · push_neg at hhn
          specialize h' (n-1)
          rw [Nat.sub_add_cancel (by omega),
          show n-1+2 = n+1 by omega] at h'
          rcases (Nat.even_or_odd n) with hn | hn
          · have: ¬ Even (n+1) := by
              refine Nat.not_even_iff_odd.mpr ?_
              exact Even.add_one hn
            rw [if_neg this]
            rw [if_pos hn] at ih
            simp only [ih, one_div, h1, sub_self, mul_zero] at h'
            field_simp [(xpos 0).ne']
            linarith only [h']
          · rw [if_neg (Nat.not_even_iff_odd.mpr hn)] at ih
            rw [if_pos (Odd.add_one hn)]
            simp only [ih, h1, sub_self, mul_zero] at h'
            field_simp [(xpos 0).ne'] at h'
            linarith only [h']
    exact (Set.eqOn_univ x fun n => if Even n then x 0 else 1 / x 0).mp fun ⦃x⦄ a => this x

  · -- verification
    rintro ⟨a, apos, hhx⟩
    intro n
    simp only [hhx]
    rcases (Nat.even_or_odd n) with hn | hn
    · have h1: Even (n+2) := by
        refine Even.add hn ?_
        exact Nat.even_iff.mpr rfl
      rw [if_pos h1, if_neg (Nat.even_add_one.mp h1), if_pos hn]
      simp [← two_mul]
    · have h1: Odd (n+2) := by
        refine Even.odd_add ?_ hn
        exact Nat.even_iff.mpr rfl
      rw [if_neg (Nat.not_even_iff_odd.mpr h1),
      if_pos (Odd.add_one hn), if_neg (Nat.not_even_iff_odd.mpr hn)]
      simp [← two_mul]