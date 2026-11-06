import Mathlib
open Real Finset Nat
set_option linter.unusedVariables false
noncomputable section

-- Lemma 1: $z(z + 3)$ mod $4$ is $0$ or $1$ implies $z$ mod $4$ is $0$ or $1$.
lemma z_mod_4 (z : ℕ) : z * (z + 3) % 4 = 0 ∨ z * (z + 3) % 4 = 1 → z % 4 = 0 ∨ z % 4 = 1 := by
  intro h
  have h_mod : z % 4 < 4 := Nat.mod_lt z (by norm_num)
  have h_cases : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
  rcases h_cases with hz0 | hz1 | hz2 | hz3
  · left; exact hz0
  · right; exact hz1
  · exfalso
    have h_z3 : (z + 3) % 4 = (z % 4 + 3) % 4 := Nat.add_mod z 3 4
    rw [hz2] at h_z3
    have : (z + 3) % 4 = 1 := by norm_num [h_z3]
    have h_prod : z * (z + 3) % 4 = (z % 4 * ((z + 3) % 4)) % 4 := Nat.mul_mod _ _ 4
    rw [hz2, this] at h_prod
    simp [norm_num] at h_prod
    cases h with
    | inl h0 => linarith
    | inr h1 => linarith
  · exfalso
    have h_z3 : (z + 3) % 4 = (z % 4 + 3) % 4 := Nat.add_mod z 3 4
    rw [hz3] at h_z3
    have : (z + 3) % 4 = 2 := by norm_num [h_z3]
    have h_prod : z * (z + 3) % 4 = (z % 4 * ((z + 3) % 4)) % 4 := Nat.mul_mod _ _ 4
    rw [hz3, this] at h_prod
    simp [norm_num] at h_prod
    cases h with
    | inl h0 => linarith
    | inr h1 => linarith

-- Lemma 2: Square mod $4$ is $0$ or $1$.
lemma square_mod_4 (y : ℕ) : y ^ 2 % 4 = 0 ∨ y ^ 2 % 4 = 1 := by
  cases Nat.mod_two_eq_zero_or_one y with
  | inl h_even =>
    have h_y_even : 2 ∣ y := Nat.dvd_of_mod_eq_zero h_even
    obtain ⟨k, rfl⟩ := h_y_even
    left
    rw [pow_two, Nat.mul_mod]
    simp [Nat.mul_mod]
    norm_num
    have : 2 * k * (2 * k) = 4 * (k * k) := by ring
    rw [this]
    omega
  | inr h_odd =>
    have h_y_odd : y % 2 = 1 := h_odd
    have : Odd y := by exact Nat.odd_iff.mpr h_y_odd
    have : Odd (y : ℤ) := by exact_mod_cast this
    have : (y : ℤ) ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd this
    right
    exact_mod_cast this

theorem number_theory_80585 {x y z : ℕ}
    (hx : x ∈ Finset.Ico 1 10) (hy : y ∈ Finset.range 10) (hz : z ∈ Finset.range 10)
    (h_eq : y ^ 2 = x * z) (h_sub : Nat.ofDigits 10 [z, y, x] - Nat.ofDigits 10 [x, y, z] = 297) :
    Nat.ofDigits 10 [z, y, x] = 300 ∨ Nat.ofDigits 10 [z, y, x] = 421 := by 
  rw [Finset.mem_Ico] at hx
  rw [Finset.mem_range] at hy
  rw [Finset.mem_range] at hz
  rcases hx with ⟨hx1, hx2⟩
  have h1 : x ≤ 9 := by
    omega
  have h2 : y ≤ 9 := by
    omega
  have h3 : z ≤ 9 := by
    omega
  simp [Nat.ofDigits] at h_sub ⊢
  all_goals norm_num at h_sub ⊢
  interval_cases x <;> try { 
    omega 
  } <;> try { 
    interval_cases y <;> try { 
      omega 
    } 
    <;> try { 
      interval_cases z <;> omega 
    } 
  }