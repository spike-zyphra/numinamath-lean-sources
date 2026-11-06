import Mathlib

/- Soit $x$ et $y$ deux entiers tels que $5 x+6 y$ et $6 x+5 y$ soient des carrés parfaits. Montrer que $x$ et $y$ sont tous deux divisibles par 11.
Note : on dit qu'un entier $n$ est un carré parfait si c'est le carré d'un entier. -/
theorem number_theory_605636 (x y : ℤ) (h₁ : ∃ n, n^2 = 5 * x + 6 * y) (h₂ : ∃ m, m^2 = 6 * x + 5 * y) :
    11 ∣ x ∧ 11 ∣ y := by
  -- Let $a$ and $b$ be integers such that $5 x + 6 y = a^2$ and $6 x + 5 y = b^2$.
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  -- show that $a² + b² = 11(x + y)$
  have h' : a ^ 2 + b ^ 2 = 11 * (x + y) := by
    linarith [ha, hb]
  -- Note that $a^2 + b^2 = 11(x + y)$ is divisible by 11
  have h₃ : (a ^ 2 + b ^ 2) % 11 = 0 := by
    rw [h']
    norm_num
  -- For all integers $k$, $k^2$ mod $11$ is equal to 0, 1, 3, 4, 5, or 9
  have h_squares_mod_11 : ∀ k : ℤ, k^2 % 11 = 0 ∨ k^2 % 11 = 1 ∨ k^2 % 11 = 3 ∨ k^2 % 11 = 4 ∨ k^2 % 11 = 5 ∨ k^2 % 11 = 9 := by
    intro k
    let k' := k % 11
    have hk' : k' = k % 11 := rfl
    have h_range : 0 ≤ k' ∧ k' < 11 := ⟨Int.emod_nonneg k (by norm_num : (11 : ℤ) ≠ 0), Int.emod_lt k (by norm_num : (11 : ℤ) ≠ 0)⟩
    have h_eq : k^2 % 11 = k'^2 % 11 := by
      rw [hk']
      simp [pow_two, Int.mul_emod, Int.add_emod]
    rw [h_eq]
    have : k' ∈ Set.Icc 0 10 := ⟨h_range.1, Int.le_of_lt_add_one h_range.2⟩
    -- Pattern match on the values of $k'$
    match k' with
    | 0 => norm_num
    | 1 => norm_num
    | 2 => norm_num
    | 3 => norm_num
    | 4 => norm_num
    | 5 => norm_num
    | 6 => norm_num
    | 7 => norm_num
    | 8 => norm_num
    | 9 => norm_num
    | 10 => norm_num
  -- Prove that $a ^ 2 % 11 = 0$ and $b ^ 2 % 11 = 0$
  have h₄ : a ^ 2 % 11 = 0 ∧ b ^ 2 % 11 = 0:= by
    have ha : a ^ 2 % 11 = 0 ∨ a ^ 2 % 11 = 1 ∨ a ^ 2 % 11 = 3 ∨ a ^ 2 % 11 = 4 ∨ a ^ 2 % 11 = 5 ∨ a ^ 2 % 11 = 9 := h_squares_mod_11 a
    have hb : b ^ 2 % 11 = 0 ∨ b ^ 2 % 11 = 1 ∨ b ^ 2 % 11 = 3 ∨ b ^ 2 % 11 = 4 ∨ b ^ 2 % 11 = 5 ∨ b ^ 2 % 11 = 9 := h_squares_mod_11 b
    have h_sum : (a ^ 2 % 11 + b ^ 2 % 11) % 11 = 0 := by rw [← Int.add_emod, h₃]
    rcases ha with (ha | ha | ha | ha | ha | ha) <;>
    rcases hb with (hb | hb | hb | hb | hb | hb) <;>
    rw [ha, hb] at h_sum <;>
    norm_num at h_sum
    tauto
  -- Express a as 11 * A
  have h₅ : ∃ A : ℤ, a = 11 * A := by
    use a / 11
    have : a % 11 + 11 * (a / 11) = a := by
      exact Int.emod_add_ediv a 11
    rw [← this]
    have : a % 11 = 0 := by
      have : 11 ∣ a^2 := by
        apply Int.dvd_of_emod_eq_zero
        exact h₄.1
      apply Int.emod_eq_zero_of_dvd
      apply Prime.dvd_of_dvd_pow (by norm_num) this
    simp [this]
  -- Express b as 11 * B
  have h₆ : ∃ B : ℤ, b = 11 * B := by
    use b / 11
    have : b % 11 + 11 * (b / 11) = b := by
      exact Int.emod_add_ediv b 11
    rw [← this]
    have : b % 11 = 0 := by
      have : 11 ∣ b^2 := by
        apply Int.dvd_of_emod_eq_zero
        exact h₄.2
      apply Int.emod_eq_zero_of_dvd
      apply Prime.dvd_of_dvd_pow (by norm_num) this
    simp [this]
  obtain ⟨A, hA⟩ := h₅
  obtain ⟨B, hB⟩ := h₆
  -- Substitute into the original equations, solve for $x$ and $y$, and prove they are multiples of $11$
  have h₇ : 11 ∣ x := by
    have eq₁ : 5 * x + 6 * y = (11 * A) ^ 2 := by rw [← ha, hA]
    have eq₂ : 6 * x + 5 * y = (11 * B) ^ 2 := by rw [← hb, hB]
    have : x = 11 * (6 * B ^ 2 - 5 * A ^ 2) := by
      linarith [eq₁, eq₂]
    rw [this]
    apply dvd_mul_right
  have h₈ : 11 ∣ y := by
    have eq₁ : 5 * x + 6 * y = (11 * A) ^ 2 := by rw [← ha, hA]
    have eq₂ : 6 * x + 5 * y = (11 * B) ^ 2 := by rw [← hb, hB]
    have : y = 11 * (6 * A ^ 2 - 5 * B ^ 2) := by
      linarith [eq₁, eq₂]
    rw [this]
    apply dvd_mul_right
  -- Final conclusion: $x$ and $y$ are both divisible by $11$
  exact ⟨h₇, h₈⟩
