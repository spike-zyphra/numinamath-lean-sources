import Mathlib

open scoped Nat

-- 9. Let $a_{1}=1, a_{2}=3$, and for all positive integers $n$, $a_{n+2}=(n+3) a_{n+1}-$ $(n+2) a_{n}$, find all values of $n$ such that $a_{n}$ is divisible by 11.
theorem algebra_213460
    (a : ℕ → ℤ)
    (h₀ : a 1 = 1)
    (h₁ : a 2 = 3)
    (h₂ : ∀ n > 0, a (n + 2) = (n + 3) * a (n + 1) - (n + 2) * a n) :
    ∀ n > 0, 11 ∣ a n ↔ n = 4 ∨ n = 8 ∨ n ≥ 10 := by
  let b n := a (n + 1) - a n
  have b_rec_eq n (n_pos : n > 0) : b (n + 1) = (n + 2) * b n := by
    specialize h₂ n n_pos
    unfold b
    linarith
  let rec b_eq : ∀ n > 0, b n = (n + 1)!
    | 1, _ => by
      unfold b
      simp [h₀, h₁]
    | n + 1, Nat.le.step n_pos => by
      change n > 0 at n_pos
      have ih := b_eq n n_pos
      norm_num [b_rec_eq n n_pos, ih]
      norm_cast
  let rec a_eq : ∀ n > 0, a n = ∑ k in Finset.Icc 1 n, k !
    | 1, _ => by
      simp
      exact h₀
    | n + 1, Nat.le.step n_pos => by
      change n > 0 at n_pos
      --specialize b_eq n n_pos
      have := b_eq n n_pos
      unfold b at this
      have : a (n + 1) = a n + (n + 1)! := by
        linarith
      rw [this]
      have ih := a_eq n n_pos
      rw [ih]
      norm_cast
      have : n + 1 ∉ Finset.Icc 1 n := by
        simp
      have sum_insert := Finset.sum_insert (f := Nat.factorial) this
      have : insert (n + 1) (Finset.Icc 1 n) = Finset.Icc 1 (n + 1) := by
        refine Nat.Icc_insert_succ_right ?_
        linarith
      rw [this] at sum_insert
      linarith
  intro n n_pos
  rw [a_eq n n_pos]
  norm_cast
  by_cases w_n_lt_10 : n < 10
  . --simp [w_n_lt_10]
    revert n_pos
    revert n
    decide
  . simp at w_n_lt_10
    simp [w_n_lt_10]
    have : 11 ∣ ∑ k ∈ Finset.Icc 1 10, k ! := by
      decide
    have eq_union : Finset.Icc 1 n = Finset.Icc 1 10 ∪ Finset.Icc 11 n := by
      ext k
      simp
      omega
    have disjoint : Disjoint (Finset.Icc 1 10) (Finset.Icc 11 n) := by
      --apply?
      intro s s_subs_left s_subs_right
      simp at s_subs_left s_subs_right
      intro k k_in_s
      specialize s_subs_left k_in_s
      specialize s_subs_right k_in_s
      simp at s_subs_left s_subs_right
      omega
    rw [eq_union]
    rw [Finset.sum_union disjoint]
    suffices (11 ∣ ∑ k ∈ Finset.Icc 11 n, k !) by
      omega
    apply Finset.dvd_sum
    intro k k_in
    simp at k_in
    have : k ≥ 11 := by
      linarith
    exact Nat.dvd_factorial (by simp) this
