import Mathlib

open Real Finset

theorem inequalities_603837 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / √(a + b) + b / √(b + c) + c / √(c + a) ≥ (√a + √b + √c) / √2 ∧
    (a / √(a + b) + b / √(b + c) + c / √(c + a) = (√a + √b + √c) / √2
    ↔ a = b ∧ b = c) := by
  rw [ge_iff_le]
  have key : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → x * y / (x + y) + y * z / (y + z) +
  z * x / (z + x) ≤ x * y / √(x + y) * (1 / √(y + z)) + y * z / √(y + z) * (1 / √(z + x))
  + z * x / √(z + x) * (1 / √(x + y)) := by
    clear a ha b hb c hc; intro x y z xpos ypos zpos
    wlog h : (z ≤ y ∧ y ≤ x) ∨ (x ≤ y ∧ y ≤ z)
    · push_neg at h; rcases h with ⟨hl, hr⟩
      rcases le_or_lt z y with h'|h'
      · specialize hl h'; specialize hr (by linarith only [hl])
        rcases le_or_lt z x with h''|h''
        · specialize this z x y zpos xpos ypos (by right; constructor; all_goals linarith)
          calc
            _ = z * x / (z + x) + x * y / (x + y) + y * z / (y + z) := by ring
            _ ≤ _ := this
            _ = _ := by ring
        specialize this y z x ypos zpos xpos (by left; constructor; all_goals linarith)
        calc
          _ = y * z / (y + z) + z * x / (z + x) + x * y / (x + y) := by ring
          _ ≤ _ := this
          _ = _ := by ring
      rw [imp_iff_or_not] at hr; rcases hr with hr|hr
      · linarith only [h', hr]
      push_neg at hr; rcases le_or_lt z x with h''|h''
      · specialize this y z x ypos zpos xpos (by right; constructor; all_goals linarith)
        calc
          _ = y * z / (y + z) + z * x / (z + x) + x * y / (x + y) := by ring
          _ ≤ _ := this
          _ = _ := by ring
      specialize this z x y zpos xpos ypos (by left; constructor; all_goals linarith)
      calc
        _ = z * x / (z + x) + x * y / (x + y) + y * z / (y + z):= by ring
        _ ≤ _ := this
        _ = _ := by ring
    rcases h with ⟨zley, ylex⟩|⟨xley, ylez⟩
    · let f : Fin 3 → ℝ := ![x * y / √(x + y),z * x / √(z + x), y * z / √(y + z)]
      let g : Fin 3 → ℝ := ![1 / √(x + y), 1 / √(z + x), 1 / √(y + z)]
      have antiv : Antivary f g := by
        rw [antivary_iff_exists_antitone_monotone]
        use Fin.instLinearOrder; simp [f, g, and_assoc]; split_ands
        · rw [mul_comm, ← mul_div, ← mul_div, mul_le_mul_left]
          rw [div_le_div_iff₀, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
          rw [mul_pow, mul_pow, sq_sqrt, sq_sqrt, ← sub_nonneg]; calc
            _ ≤ (y - z) * (x * y + y * z + z * x) := by
              apply mul_nonneg; linarith only [zley]
              positivity
            _ = _ := by ring
          all_goals positivity
        · rw [mul_comm, ← mul_div, ← mul_div, mul_le_mul_left]
          rw [div_le_div_iff₀, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
          rw [mul_pow, mul_pow, sq_sqrt, sq_sqrt, ← sub_nonneg]; calc
            _ ≤ (x - y) * (x * y + y * z + z * x) := by
              apply mul_nonneg; linarith only [ylex]
              positivity
            _ = _ := by ring
          all_goals positivity
        all_goals rw [add_comm]; gcongr
      let tofun : Fin 3 → Fin 3 := ![1, 2, 0]; let invfun : Fin 3 → Fin 3 := ![2, 0, 1]
      have left_inv : Function.LeftInverse tofun invfun := by
        intro i; simp [tofun, invfun]; fin_cases i
        all_goals simp
      have right_inv : Function.RightInverse tofun invfun := by
        intro i; simp [tofun, invfun]; fin_cases i
        all_goals simp
      let σ : Equiv.Perm (Fin 3) := Equiv.mk tofun invfun right_inv left_inv
      have RI := @Antivary.sum_mul_le_sum_comp_perm_mul (Fin 3) ℝ _ _ σ _ _ _ antiv
      simp [f, g, sum_fin_eq_sum_range, show range 3 = {0, 1, 2} by rfl] at RI
      simp [σ, tofun, invfun, ← one_div] at RI
      rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, ← add_assoc] at RI
      repeat rw [mul_one, ← pow_two, sq_sqrt] at RI
      calc
        _ = x * y / (x + y) + z * x / (z + x) + y * z / (y + z) := by ring
        _ ≤ _ := RI
        _ = _ := by ring
      all_goals positivity
    let f : Fin 3 → ℝ := ![x * y / √(x + y),z * x / √(z + x), y * z / √(y + z)]
    let g : Fin 3 → ℝ := ![1 / √(x + y), 1 / √(z + x), 1 / √(y + z)]
    have antiv : Antivary f g := by
      rw [antivary_iff_exists_monotone_antitone]
      use Fin.instLinearOrder; simp [f, g, and_assoc]; split_ands
      · nth_rw 2 [mul_comm]; rw [← mul_div, ← mul_div, mul_le_mul_left]
        rw [div_le_div_iff₀, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
        rw [mul_pow, mul_pow, sq_sqrt, sq_sqrt, ← sub_nonneg]; calc
          _ ≤ (z - y) * (x * y + y * z + z * x) := by
            apply mul_nonneg; linarith only [ylez]
            positivity
          _ = _ := by ring
        all_goals positivity
      · nth_rw 2 [mul_comm]; rw [← mul_div, ← mul_div, mul_le_mul_left]
        rw [div_le_div_iff₀, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
        rw [mul_pow, mul_pow, sq_sqrt, sq_sqrt, ← sub_nonneg]; calc
          _ ≤ (y - x) * (x * y + y * z + z * x) := by
            apply mul_nonneg; linarith only [xley]
            positivity
          _ = _ := by ring
        all_goals positivity
      all_goals rw [add_comm]; gcongr
    let tofun : Fin 3 → Fin 3 := ![1, 2, 0]; let invfun : Fin 3 → Fin 3 := ![2, 0, 1]
    have left_inv : Function.LeftInverse tofun invfun := by
      intro i; simp [tofun, invfun]; fin_cases i
      all_goals simp
    have right_inv : Function.RightInverse tofun invfun := by
      intro i; simp [tofun, invfun]; fin_cases i
      all_goals simp
    let σ : Equiv.Perm (Fin 3) := Equiv.mk tofun invfun right_inv left_inv
    have RI := @Antivary.sum_mul_le_sum_comp_perm_mul (Fin 3) ℝ _ _ σ _ _ _ antiv
    simp [f, g, sum_fin_eq_sum_range, show range 3 = {0, 1, 2} by rfl] at RI
    simp [σ, tofun, invfun, ← one_div] at RI
    rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, ← add_assoc] at RI
    repeat rw [mul_one, ← pow_two, sq_sqrt] at RI
    calc
      _ = x * y / (x + y) + z * x / (z + x) + y * z / (y + z) := by ring
      _ ≤ _ := RI
      _ = _ := by ring
    all_goals positivity
  have aux : 2 * (a / √(a + b) + b / √(b + c) + c / √(c + a)) ^ 2 - (√a + √b + √c) ^ 2 =
  4 * (a * b / √(a + b) * (1 / √(b + c)) + b * c / √(b + c) * (1 / √(c + a)) +
  c * a / √(c + a) * (1 / √(a + b)) - (a * b / (a + b) + b * c / (b + c) +
  c * a / (c + a))) + (√a - √b) ^ 4 / (2 * (a + b)) + (√b - √c) ^ 4 / (2 * (b + c))
  + (√c - √a) ^ 4 / (2 * (c + a)) := by
    repeat rw [add_sq]
    repeat rw [div_pow]
    rw [show 4 = 2*2 by simp]; repeat rw [pow_mul]
    repeat rw [sub_sq]
    repeat rw [sq_sqrt]
    repeat rw [add_sq, sub_sq]
    repeat rw [mul_pow]
    repeat rw [sq_sqrt]
    field_simp; ring
    all_goals positivity
  specialize key a b c ha hb hc;
  have pow1 : 0 ≤ (√a - √b) ^ 4 / (2 * (a + b)) := by
    apply div_nonneg; apply Even.pow_nonneg
    use 2; positivity
  have pow2 : 0 ≤ (√b - √c) ^ 4 / (2 * (b + c)) := by
    apply div_nonneg; apply Even.pow_nonneg
    use 2; positivity
  have pow3 : 0 ≤ (√c - √a) ^ 4 / (2 * (c + a)) := by
    apply div_nonneg; apply Even.pow_nonneg
    use 2; positivity
  constructor
  · rw [div_le_iff₀, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
    rw [← sub_nonneg, mul_comm, mul_pow, sq_sqrt]
    rw [aux]; linarith only [key, pow1, pow2, pow3]
    all_goals positivity
  constructor
  · intro h; rw [eq_div_iff, mul_comm] at h
    apply_fun fun t => t ^ 2 at h
    rw [mul_pow, sq_sqrt, ← sub_eq_zero, aux] at h
    replace pow1 : (√a - √b) ^ 4 / (2 * (a + b)) = 0 := by
      linarith only [h, key, pow1, pow2, pow3]
    replace pow2 : (√b - √c) ^ 4 / (2 * (b + c)) = 0 := by
      linarith only [h, key, pow1, pow2, pow3]
    rw [div_eq_zero_iff, pow_eq_zero_iff, or_comm] at pow1 pow2
    rcases pow1 with h|pow1
    · linarith only [h, ha, hb]
    rcases pow2 with h|pow2
    · linarith only [h, hc, hb]
    rw [sub_eq_zero, sqrt_inj] at pow1 pow2
    exact ⟨pow1, pow2⟩; all_goals positivity
  rintro ⟨h1, h2⟩; rw [h1, ← h2]; field_simp
  ring_nf; rw [sqrt_mul]; ring_nf
  rw [sq_sqrt]; ring; all_goals positivity