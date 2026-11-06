import Mathlib

/- Example 3 Find all positive integers $m, n$ such that $m^{2}-n$ divides $m+n^{2}$, and $n^{2}-m$ divides $n+m^{2}$.
(2002 Asia Pacific Mathematical Olympiad) -/
theorem number_theory_210851 (m n : ℤ) (hm : m > 0) (hn : n > 0) :
    m^2 - n ∣ m + n^2 ∧ n^2 - m ∣ n + m^2 ↔ 
    (m, n) = (2, 2) ∨ (m, n) = (3, 3) ∨ (m, n) = (1, 2) ∨ (m, n) = (2, 1) ∨
    (m, n) = (3, 2) ∨ (m, n) = (2, 3) := by

    constructor
    
    --From left to right. 
    intro ⟨h1,h2⟩
    
    --First, we can assume that n ≥ m.
    wlog hnm : n ≥ m
    have mgen: m ≥ n := by linarith
    have : (n, m) = (2, 2) ∨ (n, m) = (3, 3) ∨ (n, m) = (1, 2) ∨ (n, m) = (2, 1) ∨ (n, m) = (3, 2) ∨ (n, m) = (2, 3) := by 
      apply this
      repeat assumption
    simp at this
    simp
    tauto

    -- We have n ≤ m+1, since otherwise n^2-m is too large for h2.
    have nlemp1 : n ≤ m+1 := by 
      by_contra ngmp1; push_neg at ngmp1
      have : n + m^2 < n^2 -m := by nlinarith
      have : n^2 - m ≤ n + m^2 := by apply Int.le_of_dvd; nlinarith; exact h2
      linarith
    
    -- Hence, there are two cases: n = m or n = m+1. We check each case separately and verify the claim.
    by_cases neqm : n = m
    rw [← neqm] at h1
    have nle3 : n≤3 := by 
      have : n^2-n ∣ n^2 - n:= by exact Int.dvd_refl (n ^ 2 - n)
      have t1: n^2-n ∣ (n+n^2) - (n^2-n) := by exact Int.dvd_sub h1 this
      have t2 : (n+n^2) - (n^2-n) = 2 * n := by ring
      rw [t2] at t1
      have : n^2 -n ≤ 2*n := by apply Int.le_of_dvd; nlinarith; exact t1
      nlinarith
    by_cases neq1 : n=1
    rw[neq1] at h1; norm_num at h1
    by_cases neq2 : n=2
    rw [neq2] at neqm; symm at neqm; left; simp; tauto
    have neq3: n = 3 := by omega
    rw [neq3] at neqm; symm at neqm; right; left; simp; tauto

    have neqmp1: n = m+1 := by omega
    
    have : m ≤ 5 := by 
      rw [neqmp1] at h1
      have : m^2 - 5*m -3 ≤ 0 := by 
        have : m ^ 2 - (m + 1) ∣ m ^ 2 - (m + 1) := by exact Int.dvd_refl (m ^ 2 - (m + 1))
        have : m ^ 2 - (m + 1) ∣ m + (m + 1) ^ 2 - (m ^ 2 - (m + 1)) := by exact Int.dvd_sub h1 this
        ring_nf at this
        have : -1 - m + m ^ 2 ≤ 2+ m*4 := by apply Int.le_of_dvd; nlinarith; assumption
        nlinarith
      nlinarith

    by_cases meq1 : m = 1
    rw [meq1] at neqmp1; simp at neqmp1
    right;right;left; simp; tauto
    by_cases meq2: m = 2
    rw [meq2] at neqmp1;simp at neqmp1;
    right;right;right;right; right; simp; tauto
    by_cases meq3: m = 3
    rw [meq3] at neqmp1;simp at neqmp1;
    rw [meq3,neqmp1] at h1; norm_num at h1
    by_cases meq4: m = 4
    rw [meq4] at neqmp1;simp at neqmp1;
    rw [meq4,neqmp1] at h1; norm_num at h1
    have meq5 : m = 5 := by omega
    rw [meq5] at neqmp1;simp at neqmp1;
    rw [meq5,neqmp1] at h1; norm_num at h1



    --From right to left. Just simple calculation to verify everything.
    intro h
    simp at h
    rcases h with ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩ | ⟨hm,hn⟩
    simp [hm,hn]; norm_num
    simp [hm,hn]; norm_num
    simp [hm,hn]
    simp [hm,hn] 
    simp [hm,hn] 
    simp [hm,hn]