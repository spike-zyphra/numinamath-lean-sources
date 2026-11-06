import Mathlib

theorem number_theory_29628
  (a b : ℕ → ℤ)
  (ha0 : a 0 = 1)
  (ha1 : a 1 = 10)
  (han : ∀ n, a (n + 2) = 2 * a (n + 1) + 3 * a n)
  (hb0 : b 0 = 1)
  (hb1 : b 1 = 8)
  (hbn : ∀ n, b (n + 2) = 3 * b (n + 1) + 4 * b n)
  : ∀ m n,  m ≠ 0 → a m ≠ b n := by 
  -- since the sequence start from zero, then change the general formular of `a n`
  -- to be `12 * a n = (11 * 3 ^ (n + 1) + 21 * (-1) ^ (n + 1))`
  have aeq : ∀ n, (12 * a n = 11 * 3 ^ (n + 1) + 21 * (-1) ^ (n + 1) ) ∧ 
    (12 * a (n + 1) = 11 * 3 ^ (n + 2) + 21 * (-1) ^ (n + 2)) := by 
    intro n
    induction n with
    | zero => 
      constructor
      rw [ha0]
      norm_num
      simp
      rw [ha1]
      norm_num
    | succ k ih => 
      obtain ⟨ih1, ih2⟩ := ih
      constructor
      linarith
      have h1 : a (k + 1 + 1) = 2 * a (k + 1) + 3 * a k := by 
        rw [han k]
      rw [h1]
      calc 
        _ = 2 * (12 * a (k + 1)) + 3 * (12 * a k) := by ring
        _ = 2 * (11 * 3 ^ (k + 2) + 21 * (-1) ^ (k + 2)) + 3 * (11 * 3 ^ (k + 1) + 21 * (-1) ^ (k + 1)) := by rw[← ih1,← ih2]
        _ = _ := by ring
  -- similaraly, we can get this for sequence `b`.
  have beq : ∀ n, (20 * b n = 9 * 4 ^ (n + 1) + 16 * (-1) ^ (n + 1)) ∧ 
    (20 * b (n + 1) = 9 * 4 ^ (n + 2) + 16 * (-1) ^ (n + 2)) := by 
    intro n
    induction n with
    | zero =>
      constructor
      rw [hb0]
      norm_num
      simp
      rw[hb1]
      norm_num
    |  succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      constructor
      linarith
      have h1: b (k + 1 + 1) = 3 * b (k + 1) + 4 * b k := by
        rw [hbn k]
      rw [h1]
      calc
        _ = 3 * (20 * b (k + 1)) + 4 * (20 * b k) := by ring
        _ = 3 * (9 * 4 ^ (k + 2) + 16 * (-1) ^ (k + 2)) + 4 * (9 * 4 ^ (k + 1) + 16 * (-1) ^ (k + 1)) := by rw [← ih1, ← ih2]
        _ = _ := by ring
  intro n m mneq
  by_contra heq
  obtain ⟨aeq1, aeq2⟩ := aeq n
  obtain ⟨beq1, beq2⟩ := beq m
  -- if there exist $m, n$ that $a m = b n$, so $60 * a m = 60 * b n$. Then we can prove that it is impossible.
  have eq1 : 12 * a n * 5 = 20 * b m * 3 := by 
    rw [heq]
    ring
  rw [aeq1, beq1] at eq1
  by_cases hn : n > 1 
  -- cases n > 1 
  -- analysis the residual module 27
  have eq2 : 55 * 3 ^ (n + 1) + 105 * (-1) ^ (n + 1) = 27 * 4 ^ (m + 1) + 48 * (-1) ^ (m + 1) := by 
    linarith
  have nge2 : n ≥ 2 := by omega
  have n_aux : n + 1 = 3 + (n - 2) := by 
    omega
  have eq3 : 55 * (3 : ℤ) ^ (n + 1) = 55 * 27 * 3 ^ (n - 2) := by 
    rw [n_aux]
    ring_nf
  rw [eq3] at eq2
  have mod1 : 105 * (-1) ^ (n + 1) ≡ 48 * (-1) ^ (m + 1) [ZMOD 27] := by 
    calc 
      _ ≡ (55 * (27 : ℤ) * 3 ^ (n - 2) + 105 * (-1) ^ (n + 1)) [ZMOD 27] := by 
        apply Int.modEq_of_dvd
        omega
      _ ≡ 27 * 4 ^ (m + 1) + 48 * (-1) ^ (m + 1) [ZMOD 27] := by 
        exact congrFun (congrArg HMod.hMod eq2) 27
      _ ≡ 48 * (-1) ^ (m + 1) [ZMOD 27] := by 
        apply Int.modEq_of_dvd
        omega
  obtain h2 := Int.ModEq.dvd mod1
  by_cases odd_n : Odd (n + 1)
  have eq2 : (-1) ^ (n + 1) = -1 := by 
    exact Odd.neg_one_pow odd_n
  rw [eq2] at h2
  by_cases even_m : Even (m + 1)
  have eq3 : (-1) ^ (m + 1) = 1 := by
    exact Even.neg_one_pow even_m
  rw [eq3] at h2
  norm_num at h2
  simp at even_m
  have eq3 : (-1) ^ (m + 1) = -1 := by
    exact Odd.neg_one_pow even_m
  rw [eq3] at h2
  norm_num at h2
  -- cases even (n + 1)
  simp at odd_n
  have eq2 : (-1) ^ (n + 1) = 1 := by 
    exact Even.neg_one_pow odd_n
  by_cases even_m' : Even (m + 1)
  have eq3 : (-1) ^ (m + 1) = 1 := by
    exact Even.neg_one_pow even_m'
  rw [eq2, eq3] at h2
  norm_num at h2
  simp at even_m'
  have eq3 : (-1) ^ (m + 1) = -1 := by
    exact Odd.neg_one_pow even_m'
  rw [eq3, eq2] at h2
  norm_num at h2
  -- the case n > 1
  simp at hn
  interval_cases n
  simp at mneq
  simp at eq1
  have eq2 : (9 * 4 ^ (m + 1) + 16 * (-1) ^ (m + 1)) = 200 := by 
    linarith
  have bnge : ∀ n, n ≥ 2 →(b n > 10 ∧ b (n + 1) > 10) := by
    intro n hn
    induction' hn with k hk1 hk2
    constructor
    have btwo : b 2 = 3 * b 1 + 4 * b 0 := by rw[hbn 0]
    rw [btwo, hb0, hb1]
    linarith
    have bthree : b 3 = 3 * b 2 + 4 * b 1 := by rw [hbn 1]
    have btwo : b 2 = 3 * b 1 + 4 * b 0 := by rw[hbn 0]
    rw[bthree, btwo, hb0, hb1]
    linarith
    obtain ⟨hk2, hk3⟩ := hk2
    constructor
    linarith
    rw [hbn]
    linarith
  by_cases hm : m ≥ 2
  obtain bnge1 := bnge m hm
  obtain ⟨bge1, bge2⟩ := bnge1
  have ineq1 : 20 * b m > 200 := by 
    linarith
  rw [beq1, eq2] at ineq1
  linarith
  simp at hm
  interval_cases m
  norm_num at eq2
  norm_num at eq2