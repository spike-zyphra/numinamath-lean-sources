import Mathlib

lemma lemma_1 (a:ℕ→ℕ) (k:Nat) (m:Nat) (hm:m ≥ 1) (h1:∀ n ≥ 1, a n ≤ a (n + 1)) (h2: a m = a (m + k)) : ∃c:ℕ,∀(i:ℕ), i≥m→i≤m+k → a i=c := by
  use a m
  intro i hi1 hi2
  have hge: ∀ (n : ℕ), n ≥ 1 → ∀ (d : ℕ), a n ≤ a (n + d) := by
    intro n hn d
    induction d with
    | zero =>
      simp
    | succ d ih =>
      calc
        a n ≤ a (n + d) := ih
        _ ≤ a (n + d + 1) := by apply h1; omega
  have h3: i - m + m = i := by omega
  have h4: a m ≤ a i := by
    have := hge m (show m ≥ 1 by omega) (i - m)
    have add_sub_cancel: m + (i - m) = i := by omega
    rw [add_sub_cancel] at this
    exact this
  have h5: a i ≤ a m := by
    have := hge i (show i ≥ 1 by omega) (m + k - i)
    have add_sub_cancel': i + (m + k - i) = m + k := by omega
    rw [add_sub_cancel'] at this
    linarith [h2, this]
  linarith [h4, h5]

theorem number_theory_604310 : ¬∃ k : ℕ, 0 < k ∧ ∃ a : ℕ → ℕ, (∀ n ≥ 1, 0 < a n) ∧ ¬(∃ c, ∀ n ≥ 1, a n = c) ∧ ∀ n ≥ 1, a n = Nat.gcd (a (n + k)) (a (n + k + 1)) := by
  by_contra hf
  obtain ⟨k,hk,a,ha1,ha2,ha3⟩ := hf
  have h1 : ∀n≥1,∀l:ℕ,a n∣a (n+l*k) := by
    intro n hn l
    induction l with
    | zero =>
      simp
    | succ l hl =>
      have h1:= Nat.gcd_dvd_left (a (n+l*k+k)) (a (n+l*k+k+1))
      rw [←ha3 (n+l*k) (by nlinarith [hn])] at h1
      ring_nf
      exact Nat.dvd_trans hl h1
  have h2 : ∀n≥1,∀l:ℕ,a n∣a (n+l*k+l) := by
    intro n hn l
    induction l with
    | zero =>
      simp
    | succ l hl =>
      have h1:= Nat.gcd_dvd_right (a (n+l*k+l+k)) (a (n+l*k+l+k+1))
      rw [←ha3 (n+l*k+l) (by nlinarith [hn])] at h1
      ring_nf at hl
      ring_nf at h1
      ring_nf
      exact Nat.dvd_trans hl h1
  have h3 : ∀n≥1,∀m≤k-1, a n∣a (n+m*k+(m+1)) := by
    intro n hn m hm
    induction hm using Nat.decreasingInduction with
    | self=>
      have : n+(k-1)*k+(k-1+1)=n+k*k := by
        rw [Nat.sub_mul, Nat.sub_add_cancel (by linarith)]
        simp
        have : k*k≥k := by
          have : k≥1 := by linarith
          have := Nat.mul_le_mul_left k this
          simp at this
          exact this
        rw [show n+(k*k-k)+k=n+(k*k-k+k) by linarith, Nat.sub_add_cancel this]
      rw [this]
      exact h1 n hn k
    | of_succ mm hm1 hm2 =>
      -- of_succ
      have hm3 := h2 n hn (mm+1)
      rw [show n+(mm+1)*k+(mm+1+1)=n+mm*k+mm+1+k+1 by linarith] at hm2
      rw [show n+(mm+1)*k+(mm+1)=n+mm*k+mm+1+k by linarith] at hm3
      have hm4 := Nat.dvd_gcd hm3 hm2
      rw [←ha3, show n+mm*k+mm+1=n+mm*k+(mm+1)by linarith] at hm4
      exact hm4
      -- of_succ.a
      simp
  have h4 : ∀n≥1,a n∣a (n+1) := by
    intro n hn
    have := h3 n hn 0 (by linarith)
    simp at this
    exact this
  have h5 : ∀n≥1, a n = a (n+k) := by
    intro n hn
    have := ha3 n hn
    rw [Nat.gcd_eq_left (h4 (n+k) (by linarith))] at this
    exact this
  have h6 : ∀n:ℕ,n≥1→∃c:ℕ,∀(i:ℕ), i≥n→i≤n+k → a i=c := by
    intro n hn
    exact lemma_1 a k n hn (by intro n hn; exact Nat.le_of_dvd (ha1 (n+1) (by linarith)) (h4 n hn)) (h5 n hn)
  have h7 : ∃c:ℕ,∀n≥1,a n=c := by
    use a 1
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ nn hn ih =>
      obtain ⟨c,hh⟩ := h6 nn hn
      have hh1:= hh nn (by simp) (by simp)
      have hh2:= hh (nn+1) (by simp) (by simp; linarith)
      rw [←ih,hh1,hh2]
  exact ha2 h7
