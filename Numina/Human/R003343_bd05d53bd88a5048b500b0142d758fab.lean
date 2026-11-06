import Mathlib
import Mathlib.Data.Set.Lattice


def natset_min (s : Set ℕ) [DecidablePred (· ∈ s)] (min : ℕ) := min ∈ s ∧ ∀ m, m ∈ s → min ≤ m
lemma natset_min_exists (s : Set ℕ) [DecidablePred (· ∈ s)] (h : ∃ n, n ∈ s) :
    ∃ n, natset_min s n := by
  let n := Nat.find h
  have hn : n ∈ s := Nat.find_spec h
  have hmin : ∀ m, m ∈ s → n ≤ m := by
    intro m m_in_s
    exact Nat.find_le m_in_s
  exact ⟨n, hn, hmin⟩


/- Example 1 Define the function $f(n)$ on the set of positive integers as follows:
$f(n)=\left\{\begin{array}{ll}\frac{n}{2}, & \text { when } n \text { is even, } \\ n+3, & \text { when } n \text { is odd. }\end{array}\right.$
(1) Prove that for any positive integer $m$, the sequence $a_{0}=m, a_{1}=f(m), \cdots, a_{n}=f\left(a_{n-1}\right), \cdots$ always contains a term that is 1 or 3.
(2) Among all positive integers, which $m$ make the above sequence necessarily contain 3? Which $m$ make the above sequence necessarily contain 1? (1979 National High School League Question) -/
theorem number_theory_170796 :
    let f (n : ℕ) : ℕ := if Even n then n/2 else n+3
    (∀ m, 0 < m → ∃ n, f^[n] m = 1 ∨ f^[n] m = 3) ∧
    (∀ m, 0 < m → 3∣m → ∃ n, f^[n] m = 3) ∧
    (∀ m, 0 < m → ¬(3∣m) → ∃ n, f^[n] m = 1) := by

  intro f
  let seq_elems (m : ℕ) := {y | ∃ n, y = f^[n] m}
  have seq_elems_dec (m : ℕ) : DecidablePred fun x ↦ x ∈ seq_elems m := by
    exact Classical.decPred fun x ↦ x ∈ seq_elems m
  have iter_lem (m n : ℕ) : f^[n+1] m = f (f^[n] m) := by
    exact Function.iterate_succ_apply' f n m
  have f_is_pos (m : ℕ) (m_gt_0 : 0 < m) (n : ℕ) : 0 ≠ f^[n] m := by
    induction n with
    | zero => simp [f]; linarith
    | succ n ih =>
      rw [iter_lem]
      intro h
      generalize f^[n] m = x at h ih
      by_cases parity : Even x
      . have eq : (x/2)*2 = x := by exact Nat.div_two_mul_two_of_even parity
        simp [f, parity] at h
        have : 0 = x := by
          have equiv : 0 = x/2 ↔ 0 = x := by
            calc
              0 = x/2 ↔ 0*2 = (x/2)*2 := by
                exact (iff_true_right (congrFun (congrArg HMul.hMul h) 2)).mpr h
              _ ↔ 0 = (x/2)*2 := by simp
              _ ↔ 0 = x := by rw [eq]
          exact equiv.mp h
        contradiction
      . simp [f, parity] at h

  -- [1] Since $\{a_n\}$ is a sequence of natural numbers, there must be a minimum value $a_{n_0}$.
  have lem1 (m : ℕ) (m_gt_0 : 0 < m) (min : ℕ) :
      natset_min (seq_elems m) min → (min = 1 ∨ min = 3) := by
    intro h
    obtain ⟨n_min, h_n_min⟩ := h.1

    rcases Nat.lt_or_ge min 4 with h_leq_3 | h_geq_4
    . match min with
      | 0 =>
        have : 0 ≠ f^[n_min] m := by exact f_is_pos m m_gt_0 n_min
        contradiction
      | 1 => simp
      | 2 =>
        -- Also, if $a_{n_0} = 2$, then $a_{n_0+1} = 1$, which is a contradiction!
        have : 1 = f^[n_min+1] m := by
          rw [iter_lem m n_min, ← h_n_min]
          simp [f]
        have : 2 ≤ 1 := by
          exact h.2 1 (show 1 ∈ seq_elems m by use n_min+1)
        linarith
      | 3 => simp
    . by_cases min_parity : Even min
      -- If $a_{n_0} > 3$, when $a_{n_0}$ is even, $a_{{n_0}+1} = \frac{a_{n_0}}{2} < a_{n_0}$
      . have eq : f^[n_min+1] m = (f^[n_min] m)/2 := by
          rw [iter_lem m n_min, ← h_n_min]
          simp [f]
          intro min_is_odd
          rw [← Nat.not_odd_iff_even] at min_parity
          contradiction
        have : min/2 < min := by
          refine Nat.bitwise_rec_lemma ?_; exact Nat.not_eq_zero_of_lt h_geq_4
        have : min ≤ min/2 := by
          apply h.2 (min/2)
          use n_min+1
          rw [h_n_min, ← eq]
        linarith
      -- when $a_{n_0}$ is odd, $a_{{n_0}+2} = \frac{a_{n_0} + 3}{2} < a_{n_0}$.
      . have eq : f^[n_min+2] m = ((f^[n_min] m)+3)/2 := by
          rw [iter_lem m (n_min+1)]
          rw [iter_lem m n_min, ← h_n_min]
          simp [f, min_parity]
          intro min_plus_3_is_odd
          have min_is_odd : Odd min := by
            exact Nat.not_even_iff_odd.mp min_parity
          have min_plus_3_is_even : Even (min+3) := by
            refine Odd.add_odd min_is_odd ?_
            exact Nat.odd_iff.mpr rfl
          rw [← Nat.not_odd_iff_even] at min_plus_3_is_even
          contradiction
        have : (min+3)/2 < min := by exact Nat.avg_lt_left h_geq_4
        have : min ≤ (min+3)/2 := by
          apply h.2 ((min+3)/2)
          use n_min+2
          rw [h_n_min, ← eq]
        linarith
  -- Therefore, $a_{n_0}$ must be equal to 1 or 3.
  have part1 : ∀ m, 0 < m → ∃ n, f^[n] m = 1 ∨ f^[n] m = 3 := by
    intro m m_gt_0
    obtain ⟨min, h_min⟩ := by
      apply natset_min_exists (seq_elems m)
      use m
      use 0
      simp
    obtain ⟨min_n, h_min_n⟩ := by exact h_min.1
    use min_n
    rw [← h_min_n]
    apply lem1 m m_gt_0 min
    exact h_min

  refine ⟨?_, ?_, ?_⟩
  . exact part1

  -- [2] From the definition of $f(n)$, it is easy to see that if $3 \mid a_0$ then $3 \mid a_{n}$, $n = 1, 2, \ldots$.
  . have lem2 (m : ℕ) (m_gt_0 : 0 < m) : 3∣m → ∀n, 3∣(f^[n] m) := by
      intro hm n
      induction n with
      | zero => simp ; exact hm
      | succ n ih =>
        rw [iter_lem m n]
        generalize hx : f^[n] m = x
        rw [hx] at ih
        by_cases parity : Even x
        . simp [f, parity]
          apply Nat.dvd_div_of_mul_dvd
          refine Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl ?_ ih
          exact even_iff_two_dvd.mp parity
        . simp [f, parity]; exact ih

    intro m m_pos hm
    obtain ⟨n,disj⟩ := part1 m m_pos
    -- Therefore, the sequence $\{a_n\}$ does not contain any term equal to 1, and by [1], it must contain a term equal to 3.
    rcases disj with h | h
    . have : 3∣1 := by
        rw [← h]
        apply lem2 m m_pos hm
      contradiction
    . use n
  -- If $3 \nmid a_0$, then $3 \nmid a_n$ for $n = 1, 2, \ldots$.
  . have lem2 (m : ℕ) (m_gt_0 : 0 < m) : ¬3∣m → ∀n, ¬3∣(f^[n] m) := by
      intro hm n
      induction n with
      | zero => simp; exact hm
      | succ n ih =>
        rw [iter_lem m n]
        generalize hx : f^[n] m = x
        rw [hx] at ih
        by_cases parity : Even x
        . simp [f, parity]
          intro h
          have : 3∣x := by
            obtain ⟨k,hk⟩ := by exact even_iff_two_dvd.mp parity
            rw [hk] at h
            have hcancel : 2 * k / 2 = k := by
              exact Nat.mul_div_right k Nat.zero_lt_two
            rw [hcancel] at h
            rw [hk]
            exact (Nat.Coprime.dvd_mul_left rfl).mpr h
          contradiction
        . simp [f, parity]; exact ih

    intro m m_pos hm
    obtain ⟨n,disj⟩ := part1 m m_pos
    -- Hence the sequence $\{a_n\}$ does not contain any term equal to 3, and by [1], it must contain a term equal to 1.
    rcases disj with h | h
    . use n
    . have : ¬3∣3 := by
        nth_rw 2 [← h]
        apply lem2 m m_pos hm
      contradiction