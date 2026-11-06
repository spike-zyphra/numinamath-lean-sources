import Mathlib

/-We need the following lemma on cubes modulo $7$-/
lemma lm1 (n : ℕ) : n ^ 3 ≡ 0 [MOD 7] ∨ n ^ 3 ≡ 1 [MOD 7] ∨ n ^ 3 ≡ 6 [MOD 7] := by
  have hr := Nat.mod_lt n (show 7>0 by norm_num)
  have hn1 : n ^ 3 ≡ (n % 7) ^ 3 [MOD 7] := by
    apply Nat.ModEq.pow; rw [Nat.ModEq.comm]; apply Nat.mod_modEq
-- Case by case study on the value of the remainder $n%7$
  by_cases h0 : n % 7 = 0; left; rw [h0] at hn1; simp at hn1; assumption
  by_cases h1 : n % 7 = 1; right; left; rw [h1] at hn1; simp at hn1; assumption
  by_cases h2 : n % 7 = 2
  · right; left; rw [h2] at hn1; simp at hn1
    have : 8 ≡ 1 [MOD 7] := by rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
    exact Nat.ModEq.trans hn1 this
  by_cases h3 : n % 7 = 3
  · right; right; rw [h3] at hn1; simp at hn1
    have : 27 ≡ 6 [MOD 7] := by rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
    exact Nat.ModEq.trans hn1 this
  by_cases h4 : n % 7 = 4
  · right; left; rw [h4] at hn1; simp at hn1
    have : 64 ≡ 1 [MOD 7] := by rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
    exact Nat.ModEq.trans hn1 this
  by_cases h5 : n % 7 = 5
  · right; right; rw [h5] at hn1; simp at hn1
    have : 125 ≡ 6 [MOD 7] := by rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
    exact Nat.ModEq.trans hn1 this
  by_cases h6 : n % 7 = 6
  · right; right; rw [h6] at hn1; simp at hn1
    have : 216 ≡ 6 [MOD 7] := by rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
    exact Nat.ModEq.trans hn1 this
  push_neg at *; rw [Nat.lt_iff_le_pred] at hr; simp at hr
  replace hr := Nat.lt_iff_le_and_ne.mpr ⟨hr, h6⟩
  rw [Nat.lt_iff_le_pred] at hr; simp at hr
  replace hr := Nat.lt_iff_le_and_ne.mpr ⟨hr, h5⟩
  rw [Nat.lt_iff_le_pred] at hr; simp at hr
  replace hr := Nat.lt_iff_le_and_ne.mpr ⟨hr, h4⟩
  rw [Nat.lt_iff_le_pred] at hr; simp at hr
  replace hr := Nat.lt_iff_le_and_ne.mpr ⟨hr, h3⟩
  rw [Nat.lt_iff_le_pred] at hr; simp at hr
  replace hr := Nat.lt_iff_le_and_ne.mpr ⟨hr, h2⟩
  rw [Nat.lt_iff_le_pred] at hr; simp at hr
  replace hr := Nat.lt_iff_le_and_ne.mpr ⟨hr, h1⟩
  rw [Nat.lt_iff_le_pred] at hr; simp at hr; contradiction
  norm_num; norm_num; norm_num; norm_num; norm_num; norm_num; norm_num

/-We need the following lemma on powers of $2$ modulo $7$-/
lemma lm2 (n : ℕ) : 2 ^ (3 * n) ≡ 1 [MOD 7] ∧ 2 ^ (3 * n + 1) ≡ 2 [MOD 7] ∧
2 ^ (3 * n + 2) ≡ 4 [MOD 7] := by
  have h0 : 2 ^ (3 * n) ≡ 1 [MOD 7] := by
    rw [pow_mul, show 2^3=8 by simp, show 1=1^n by simp]
    apply Nat.ModEq.pow; rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
  have h1 : 2 ^ (3 * n + 1) ≡ 2 [MOD 7] := by
    rw [pow_add]; simp; nth_rw 3 [show 2=1*2 by simp]
    apply Nat.ModEq.mul; assumption; rfl
  have h2 : 2 ^ (3 * n + 2) ≡ 4 [MOD 7] := by
    rw [pow_add]; simp; nth_rw 2 [show 4=1*4 by simp]
    apply Nat.ModEq.mul; assumption; rfl
  exact ⟨h0, h1, h2⟩

/-Prove that the equation  $2^x + 21^x = y^3$  has no solution in the set of natural numbers.-/
theorem number_theory_8489 :
¬ ∃ (x y : ℕ), 2 ^ x + 21 ^ x = y ^ 3 := by
  rintro ⟨x, y, hxy⟩
-- Prepare some simple facts for later use
  have hy0 : 1 ≤ y := by
    by_contra h'; simp at h'; rw [h'] at hxy; simp at hxy
  have hx0 : 1 ≤ x := by
    by_contra h'; simp at h'; rw [h'] at hxy; simp at hxy
    by_cases h'' : 2 ≤ y
    · have : 2 ^ 3 ≤ y ^ 3 := by
        rw [Nat.pow_le_pow_iff_left]; assumption; norm_num
      linarith
    simp at h'';
    have : y = 1 := by linarith
    rw [this] at hxy; linarith
  have h21 : 21 ^ x ≡ 0 [MOD 7] := by
    rw [Nat.modEq_zero_iff_dvd, Prime.dvd_pow_iff_dvd]; norm_num
    rw [← Nat.prime_iff]; norm_num; linarith
  have hx1 := Nat.mod_add_div x 3
  have hr := Nat.mod_lt x (show 3>0 by norm_num)
  have hx2 := lm2 (x/3)
  have hy1 := lm1 y
-- Case to case study on the value of the remainder $x%3$
  by_cases xr0 : x % 3 = 0
-- If $x%3$ equals $0$, we will be able to construct a solution to the famous Fermat Last Theorem in case $3$, which is a contradiction
  · rw [xr0] at hx1; simp at hx1
    rw [← hx1, mul_comm, pow_mul, pow_mul] at hxy;
    have u1 : 2 ^ (x / 3) ≠ 0 := by rw [← Nat.pos_iff_ne_zero]; apply Nat.pow_pos; norm_num
    have u2 : 21 ^ (x / 3) ≠ 0 := by rw [← Nat.pos_iff_ne_zero]; apply Nat.pow_pos; norm_num
    have := (fermatLastTheoremThree (2 ^ (x / 3)) (21 ^ (x / 3)) y) u1 u2 (show y≠0 by linarith)
    contradiction

-- Case $x%3$ equals $1$, we will find a contradiction modulo $7$
  by_cases xr1 : x % 3 = 1
  · rw [xr1] at hx1
    have v1 : 2 ^ x ≡ 2 [MOD 7] := by rw [← hx1, add_comm]; exact hx2.right.left
    have v2 : y ^ 3 ≡ 2 [MOD 7] := by
      rw [← hxy]; nth_rw 2 [show 2=2+0 by simp]; apply Nat.ModEq.add
      assumption; assumption
    rcases hy1 with h | h | h
    · rw [Nat.ModEq.comm] at h
      have := Nat.ModEq.trans h v2
      rw [Nat.modEq_iff_dvd'] at this; contradiction; norm_num
    · rw [Nat.ModEq.comm] at h
      have := Nat.ModEq.trans h v2
      rw [Nat.modEq_iff_dvd'] at this; contradiction; norm_num
    rw [Nat.ModEq.comm] at v2
    have := Nat.ModEq.trans v2 h
    rw [Nat.modEq_iff_dvd'] at this; contradiction; norm_num

-- Case $x%3$ equals $2$, we will find a contradiction modulo $7$
  by_cases xr2 : x % 3 = 2
  · rw [xr2] at hx1
    have w1 : 2 ^ x ≡ 4 [MOD 7] := by rw [← hx1, add_comm]; exact hx2.right.right
    have w2 : y ^ 3 ≡ 4 [MOD 7] := by
      rw [← hxy]; rw [show 4=4+0 by simp]; apply Nat.ModEq.add
      assumption; assumption
    rcases hy1 with h | h | h
    · rw [Nat.ModEq.comm] at h
      have := Nat.ModEq.trans h w2
      rw [Nat.modEq_iff_dvd'] at this; contradiction; norm_num
    · rw [Nat.ModEq.comm] at h
      have := Nat.ModEq.trans h w2
      rw [Nat.modEq_iff_dvd'] at this; contradiction; norm_num
    rw [Nat.ModEq.comm] at w2
    have := Nat.ModEq.trans w2 h
    rw [Nat.modEq_iff_dvd'] at this; contradiction; norm_num
  push_neg at *; rw [Nat.lt_iff_le_pred] at hr; simp at hr
  replace hr := Nat.lt_iff_le_and_ne.mpr ⟨hr, xr2⟩
  rw [Nat.lt_iff_le_pred] at hr; simp at hr
  replace hr := Nat.lt_iff_le_and_ne.mpr ⟨hr, xr1⟩
  simp at hr; contradiction; norm_num; norm_num