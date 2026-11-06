import Mathlib
open Nat Finset Function
noncomputable section

-- Defines the function $f(n)$.
def f (n : ℕ) : ℕ := if Even n then n / 2 else n + 3

-- Defines the sequence $a_n$.
def f_seq (m : ℕ) : ℕ → ℕ
  | 0 => m
  | succ n => f (f_seq m n)

-- Lemma: Proves the existence of a sequence value smaller than a given minimum $a_n0$.
lemma smaller_value_exists (m : ℕ) (a_n0 n0 : ℕ) (h_n0 : f_seq m n0 = a_n0) (h_positive : ∀ k ∈  { k | ∃ n, f_seq m n = k }, k > 0)
  (h_a_n0_ge_4 : a_n0 ≥ 4) : ∃ n', f_seq m n' < a_n0 ∧ f_seq m n' ∈  { k | ∃ n, f_seq m n = k } := by
  -- Consider the parity of $a_n0$.
  by_cases h_even : Even a_n0
  · -- Even case: Choose $n' = n0 + 1$, f_seq $m (n0 + 1) = a_n0 / 2 < a_n0$.
    use n0 + 1
    constructor
    · rw [f_seq, f, h_n0, if_pos h_even]
      exact Nat.div_lt_self (h_positive a_n0 ⟨n0, h_n0⟩) (by norm_num)
    · exists n0 + 1
  · -- Odd case: Choose $n' = n0 + 2$, f_seq $m (n0 + 2) = (a_n0 + 3) / 2 < a_n0$.
    use n0 + 2
    have h_f_a_n0 : f_seq m (n0 + 1) = f a_n0 := by rw [f_seq, h_n0]
    have h_f_a_n0_val : f a_n0 = a_n0 + 3 := by
      rw [f]
      split_ifs
      rfl
    have h_f_f_a_n0_val : f (f a_n0) = (a_n0 + 3) / 2 := by
      rw [h_f_a_n0_val, f]
      have h_odd : Odd a_n0 := Nat.not_even_iff_odd.mp h_even
      have h_odd3 : Odd 3 := by decide
      have : Even (a_n0 + 3) := Odd.add_odd h_odd h_odd3
      rw [if_pos this]
    constructor
    · rw [f_seq, h_f_a_n0, h_f_f_a_n0_val]
      apply Nat.div_lt_of_lt_mul
      have : a_n0 + 3 < 2 * a_n0 := by omega
      exact this
    · exists n0 + 2

/-$8 \cdot 52$ Define the function $f(n)$ on the set of positive integers as follows:
$$
f(n)=\left\{\frac{n}{2}, n+3,\right.
$$
when $n$ is even,
when $n$ is odd,
(1) Prove that for any positive integer $m$, the sequence
$$
a_{0}=m, a_{1}=f(m), \cdots, a_{n}=f\left(a_{n-1}\right), \cdots
$$
always contains a term that is 1 or 3.
(2) Among all positive integers, which $m$ make the above sequence necessarily contain 3? Which $m$ make the above sequence necessarily contain 1?-/
theorem number_theory_178946 (m : ℕ) (hm : 0 < m) :
    (∃ n, f_seq m n = 1 ∨ f_seq m n = 3) ∧
    ((3 ∣ m → (∃ n, f_seq m n = 3) ∧ (∀ n, f_seq m n ≠ 1)) ∧
     (¬3 ∣ m → (∃ n, f_seq m n = 1) ∧ (∀ n, f_seq m n ≠ 3))) := by
  -- Prove the sequence contains $1$ or $3$.
  have h_part1 : ∃ n, f_seq m n = 1 ∨ f_seq m n = 3 := by
    -- Assume the sequence does not contain $1$ or $3$.
    by_contra h_contra
    push_neg at h_contra
    let s := { k | ∃ n, f_seq m n = k }
    -- Prove s is nonempty.
    have h_nonempty : s.Nonempty := by
      use m
      exists 0
    -- Prove all values in $s$ are positive.
    have h_positive : ∀ k ∈ s, k > 0 := by
      intros k hk
      rcases hk with ⟨n, hn⟩
      have h_seq_pos : ∀ n, f_seq m n > 0 := by
        intro n
        induction' n with n ih
        · rw [f_seq]
          exact hm
        · rw [f_seq, f]
          split_ifs with h
          · exact Nat.div_pos (Nat.le_of_dvd ih (by exact Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp h))) (by omega)
          · omega
      rw [← hn]
      exact h_seq_pos n
    -- Construct the minimum value of $s$.
    have h_s_min : ∃ k ∈ s, ∀ k' ∈ s, k ≤ k' := by
      obtain ⟨a_n0, h_a_n0_in_s, hmin⟩ := WellFounded.has_min Nat.lt_wfRel.wf s h_nonempty
      refine ⟨a_n0, h_a_n0_in_s, fun k' hk' => le_of_not_lt (hmin k' hk')⟩
    obtain ⟨a_n0, h_a_n0_in_s, h_min⟩ := h_s_min
    rcases h_a_n0_in_s with ⟨n0, h_n0⟩
    have h_a_n0_pos : a_n0 > 0 := h_positive a_n0 ⟨n0, h_n0⟩
    have h_a_n0_not_1_or_3 : a_n0 ≠ 1 ∧ a_n0 ≠ 3 := by rw [← h_n0];exact h_contra n0
    have h_a_n0_ge_2 : a_n0 ≥ 2 := by omega
    have h_a_n0_not_2 : a_n0 ≠ 2 := by
      intro h_eq
      have : f_seq m (n0 + 1) = 1 := by
        rw [f_seq, f]
        rw [← h_n0] at h_eq
        simp [h_eq]
      have : f_seq m (n0 + 1) ≠  1 := (h_contra (n0 + 1)).1
      contradiction
    have h_a_n0_ge_4 : a_n0 ≥ 4 := by omega
    have h_smaller : ∃ n', f_seq m n' < a_n0 ∧ f_seq m n' ∈ s :=
      smaller_value_exists m a_n0 n0 h_n0 h_positive h_a_n0_ge_4
    -- Destructure to obtain $n'$.
    obtain ⟨n', h_smaller_n', h_in_s⟩ := h_smaller
    have h_n_ge_a_n0 : a_n0 ≤ f_seq m n' := h_min (f_seq m n') h_in_s
    have : f_seq m n' < f_seq m n' := Nat.lt_of_lt_of_le h_smaller_n' h_n_ge_a_n0
    linarith
  -- Analyze divisibility by $3$.
  have h_part2 : (3 ∣ m → (∃ n, f_seq m n = 3) ∧ (∀ n, f_seq m n ≠ 1)) ∧
                 (¬3 ∣ m → (∃ n, f_seq m n = 1) ∧ (∀ n, f_seq m n ≠ 3)) := by
    constructor
    · -- If $3 | m$, sequence contains $3$ and not $1$.
      intro h_div
      have h_div_all : ∀ n, 3 ∣ f_seq m n := by
        intro n
        induction' n with n ih
        · exact h_div
        · rw [f_seq, f]
          split_ifs with h
          · have : 2 ∣ f_seq m n := Even.two_dvd h
            have : Nat.Coprime 2 3 := by norm_num
            have : 2 * 3 ∣ f_seq m n := by omega
            exact Nat.dvd_div_of_mul_dvd this
          · apply Nat.dvd_add ih
            use 1
      constructor
      · -- Sequence contains $3$.
        have : ∃ n, f_seq m n = 1 ∨ f_seq m n = 3 := h_part1
        rcases this with ⟨n, h1 | h3⟩
        · have : 3 ∣ f_seq m n := h_div_all n
          rw [h1] at this
          contradiction
        · use n
      · -- Sequence does not contain $1$
        intro n h_eq
        have : 3 ∣ f_seq m n := h_div_all n
        rw [h_eq] at this
        contradiction
    · -- -- If $3 ∤ m$, sequence contains $1$ and not $3$.
      intro h_not_div
      have h_not_div_all : ∀ n, ¬3 ∣ f_seq m n := by
        intro n
        induction' n with n ih
        · exact h_not_div
        · rw [f_seq, f]
          split_ifs with h
          · have : 2 ∣ f_seq m n := Even.two_dvd h
            have : Nat.Coprime 2 3 := by norm_num
            intro h_div
            have : 3 ∣ f_seq m n := by omega
            contradiction
          · intro h_div
            have : 3 ∣ f_seq m n := by omega
            contradiction
      constructor
      · -- Sequence contains $1$.
        have : ∃ n, f_seq m n = 1 ∨ f_seq m n = 3 := h_part1
        rcases this with ⟨n, h1 | h3⟩
        · use n
        · have : 3 ∣ f_seq m n := by
            rw [h3]
          have : ¬3 ∣ f_seq m n := h_not_div_all n
          contradiction
      · -- Sequence does not contain $3$.
        intro n h_eq
        have : 3 ∣ f_seq m n := by
          rw [h_eq]
        have : ¬3 ∣ f_seq m n := h_not_div_all n
        contradiction
  -- Combine results.
  exact ⟨h_part1, h_part2⟩
