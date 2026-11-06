import Mathlib

/- Consider the sequences $\left(a_{n}\right),\left(b_{n}\right)$ defined by $a_{1}=3, b_{1}=100,
  a_{n+1}=3^{a_{n}}, b_{n+1}= 100^{b_{n}}$. Find the smallest integer $m$ for which $b_{m}>a_{100}$.
  Answer: 99 -/
theorem other_23725 (a b : ℕ → ℕ) (ha : a 1 = 3) (hb : b 1 = 100)
    (ha' : ∀ n ≥ 1, a (n + 1) = 3 ^ a n) (hb' : ∀ n ≥ 1, b (n + 1) = 100 ^ b n) :
    IsLeast {m | 1 ≤ m ∧ b m > a 100} 99 := by

  constructor
  · -- First we prove that $99$ satisfies the requirements.
    simp only [gt_iff_lt, Set.mem_setOf_eq, Nat.one_le_ofNat, true_and]
    -- Since $b_{1}=100>27=a_{2}$, inductively $b_{j}=100^{b_{j-1}}>3^{b_{j-1}}>3^{a_{j}}=a_{j+1}$
    -- and hence $m \leq 99$.
    have (j : ℕ) : a (j + 2) < b (j + 1) := by
      induction' j with j hi
      · rw [hb, ha' 1 (by omega), ha]
        decide
      · calc
          _ = 3 ^ (a (j + 2)) := by rw [show j + 1 + 2 = j + 2 + 1 by omega, ha' (j + 2) (by omega)]
          _ < 3 ^ (b (j + 1)) := (Nat.pow_lt_pow_iff_right (by omega)).mpr hi
          _ < 100 ^ (b (j + 1)) := Nat.pow_lt_pow_left (by omega) (Nat.not_eq_zero_of_lt hi)
          _ = _ := by rw [hb' (j + 1) (by omega)]
    exact this 98

  · -- Now we prove that no integer less that $99$ satisfies the requirements.
    simp only [gt_iff_lt]
    rintro m ⟨hm, hab⟩

    -- For any $j$, $b_j > 12$.
    have hb'' (j : ℕ) : 12 < b (j + 1) := by
      rcases (by omega : j = 0 ∨ 1 ≤ j) with hc | hc
      · rw [hc, hb]; omega
      · rw [hb' j hc]
        have : 1 ≤ b j := by
          obtain ⟨k, hk⟩ := Nat.le.dest hc; rw [← hk]
          rcases (by omega : k = 0 ∨ 1 ≤ k) with hc' | hc'
          · rw [hc', add_zero, hb]; omega
          · rw [← show k + 1 = 1 + k by omega, hb' k hc']
            exact Nat.one_le_pow' (b k) 99
        refine Nat.lt_of_lt_of_le (show 12 < 100 by omega) ?_
        exact (Nat.pow_le_pow_iff_right (show 1 < 100 by omega)).mpr this

    -- We note that $\left(b_{1}\right)^{2}=10^{4}<27^{4}=3^{12}<3^{27}=a_{3}$.
    -- We also note for $d>12$ that if $c>d^{2}$, then
    -- $3^{c}>3^{d^{2}}>3^{12 d}=\left(3^{12}\right)^{d}>10000^{d}=\left(100^{d}\right)^{2}$
    -- Hence from $a_{3}>\left(b_{1}\right)^{2}$ it inductively follows that
    -- $a_{j}>\left(b_{j-2}\right)^{2}>b_{j-2}$ and hence that $b_{99}>a_{100}>b_{98}$.
    have h_bdd (j : ℕ) : (b (j + 1)) ^ 2 < a (j + 3) := by
      induction' j with j ih
      · rw [zero_add, hb, ha' 2 (by omega), ha' 1 (by omega), ha]; simp
      · calc
          _ = (100 ^ (b (j + 1))) ^ 2 := by rw [hb' (j + 1) (by omega)]
          _ = 10000 ^ (b (j + 1)) := by
            rw [pow_two, show 10000 = 100 * 100 by omega]
            exact Eq.symm (Nat.mul_pow 100 100 (b (j + 1)))
          _ < (3 ^ 12) ^ (b (j + 1)) := by
            exact Nat.pow_lt_pow_left (by omega) <| Nat.not_eq_zero_of_lt (hb'' j)
          _ = 3 ^ (12 * (b (j + 1))) := Eq.symm (Nat.pow_mul 3 12 (b (j + 1)))
          _ < 3 ^ ((b (j + 1)) ^ 2) := by
            refine (Nat.pow_lt_pow_iff_right (by omega)).mpr ?_
            rw [pow_two]
            exact Nat.mul_lt_mul_of_pos_right (hb'' j) (Nat.zero_lt_of_lt (hb'' j))
          _ < 3 ^ (a (j + 3)) := (Nat.pow_lt_pow_iff_right (by omega)).mpr ih
          _ = _ := by rw [ha' (j + 3) (by omega)]

    -- An estimate concerning integers which is required shortly
    have le_pow_of_two_le (m : ℕ) {n : ℕ} (h : 2 ≤ n) : m ≤ n ^ m := by
      induction m with
      | zero => simp
      | succ m ih => calc
          _ ≤ n ^ m + 1 := Nat.add_one_le_add_one_iff.mpr ih
          _ ≤ 2 * n ^ m := add_one_le_two_mul <| Nat.one_le_pow m n <| Nat.zero_lt_of_lt h
          _ ≤ n * n ^ m := Nat.mul_le_mul_right (n ^ m) h
          _ = _ := Eq.symm Nat.pow_succ'

    -- The sequence $b_n$ is monotone.
    have h_mono {m : ℕ} {n : ℕ} : 1 ≤ m → 1 ≤ n → m ≤ n → b m ≤ b n := by
      have succ (n : ℕ) : 1 ≤ n → b n ≤ b (n + 1) := by
        intro hn
        rw [hb' n hn]
        exact le_pow_of_two_le (b n) (show 2 ≤ 100 by omega)
      intro hm hn hmn
      rcases Nat.le.dest hmn with ⟨k, hk⟩
      rw [← hk]; clear hk
      induction' k with k ih
      · simp
      · calc
          _ ≤ b (m + k) := ih
          _ ≤ _ := succ (m + k) (by omega)

    -- Using the above estimates we show that no integer less that $99$ satisfies the requirements.
    by_contra hc; push_neg at hc
    have : b m < b m := calc
      _ ≤ b 98 := h_mono hm (by omega) (show m ≤ 98 by omega)
      _ ≤ (b 98) ^ 2 := by
        nth_rw 1 [show b 98 = 1 * (b 98) by omega, pow_two]
        exact Nat.mul_le_mul_right (b 98) (Nat.one_le_of_lt (hb'' 97))
      _ < a 100 := h_bdd 97
      _ < _ := hab
    exact (lt_self_iff_false _).mp this
