import Mathlib

open scoped BigOperators

def S_prop (n : ℕ) : Prop :=
  n ≥ 3 ∧
  ∃ p : Fin n → ℕ,
    (∀ i, Odd (p i)) ∧
    (∀ i, Nat.Prime (p i)) ∧
    (∀ i, p i < 180) ∧
    (∑ i, p i) = (n - 2) * 180

def S : Set ℕ := {n | S_prop n}

lemma general_sum_odd_iff_odd_n (n : ℕ) (p : Fin n → ℕ) (hp : ∀ i, Odd (p i)) :
    Odd (∑ i, p i) ↔ Odd n := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    have h_last_odd : Odd (p (Fin.last k)) := by
      apply hp
    have h_first_k_terms_hp : ∀ (i : Fin k), Odd (p (Fin.castSucc i)) := by
      intro i
      apply hp
    specialize ih (fun i => p (Fin.castSucc i)) h_first_k_terms_hp
    rw [Nat.odd_add]
    simp
    rw [Fin.sum_univ_castSucc p]
    rw [Nat.odd_add]
    rw [ih]
    have h_last_even_is_false : Even (p (Fin.last k)) ↔ False := by
      simp [h_last_odd, Nat.not_even_iff_odd]
    rw [h_last_even_is_false]
    simp

theorem my_favorite_theorem :
  IsGreatest S 360 ∧ IsLeast S 4 := by
  constructor
  ·
    constructor
    simp [S,S_prop]
    use fun i ↦ 179
    simp
    native_decide
    intro x hx
    rcases hx with ⟨hn_ge_3, p, _hp_odd, _hp_prime, hp_lt_180, h_sum⟩
    have hp_le_179 : ∀ i, p i ≤ 179 := by
        intro i
        exact Nat.le_of_lt_succ (hp_lt_180 i)
    have h_sum_le_n_times_179 : (∑ i, p i) ≤ x * 179 := by
      have h1 : ∀ i : Fin x, p i ≤ (179 : ℝ) := by
        intro i
        specialize hp_le_179  i
        simpa using hp_le_179 
      have h2 : ∑ i : Fin x, p i ≤ ∑ i : Fin x, (179 : ℝ) := by
        norm_cast
        apply Finset.sum_le_sum
        intro i hi
        have := h1 i
        simpa using this
      have h3 : ∑ i : Fin x, (179 : ℝ) = (179 : ℝ) * x := by
        simp [Finset.sum_const, Finset.card_univ, mul_comm]
      rw [h3] at h2
      rw [mul_comm] at h2
      norm_cast at h2 ⊢
    rw [h_sum] at h_sum_le_n_times_179
    have hn_ge_2 : x ≥ 2 := Nat.le_trans (by norm_num : 2 ≤ 3) hn_ge_3
    rw [Nat.sub_mul,
        show 180 = 179 + 1 by norm_num,
        Nat.left_distrib x 179 1,
        Nat.mul_one x] at h_sum_le_n_times_179
    have h_sub_condition : x * 179 + x ≥ 360 := by
      calc x * 179 + x = x * (179 + 1) := by ring
                      _ = x * 180       := by norm_num
                      _ ≥ 3 * 180       := Nat.mul_le_mul_right 180 hn_ge_3 -- n ≥ 3
                      _ = 540           := by norm_num
                      _ ≥ 360           := by norm_num
    rw [Nat.sub_le_iff_le_add] at h_sum_le_n_times_179
    exact Nat.add_le_add_iff_left.mp h_sum_le_n_times_179

  · constructor
    simp [S,S_prop]
    let p_4 : Fin 4 → ℕ := ![7, 173, 7, 173]
    use p_4
    native_decide
    intro n hn_in_S
    rcases hn_in_S with ⟨hn_ge_3, p, hp_odd, _hp_prime, _hp_lt_180, h_sum⟩
    have h_sum_parity : Odd (∑ i, p i) ↔ Odd n := by
      apply general_sum_odd_iff_odd_n
      exact hp_odd
    have h_rhs_even : Even ((n - 2) * 180) := by
      exact ⟨(n - 2) * 90, by ring⟩
    rw [h_sum] at h_sum_parity
    have h_not_even_is_false : ¬Even ((n - 2) * 180) ↔ False := by
      simp [h_rhs_even]
    rw [←Nat.not_even_iff_odd, h_not_even_is_false] at h_sum_parity
    simp at h_sum_parity
    by_contra h'
    push_neg at h'
    have h3 : n = 3 := by omega
    rw [h3] at h_sum_parity
    have h4 : ¬ Even 3 := by
      norm_num [Nat.even_iff] 
    contradiction