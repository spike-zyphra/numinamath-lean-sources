import Mathlib

/- Show that there exists a positive integer $N$ such that for all integers $a>N$, there exists a contiguous substring of the decimal expansion of $a$ that is divisible by 2011. (For instance, if $a=153204$, then 15, 532, and 0 are all contiguous substrings of $a$. Note that 0 is divisible by 2011 .)-/
theorem number_theory_605548 : ∃ N : ℕ, ∀ a > N, ∃ i j, i < j ∧ j < (Nat.digits 10 a).length ∧
    2011 ∣ ∑ k ∈ Finset.Ico i j, 10 ^ (k - i) * (Nat.digits 10 a)[k]! := by
  -- We claim that if the decimal expansion of (a) has at least 2012 digits,
  -- then (a) contains the required substring.
  -- Hence we can choose `N=10^2011`.
  use 10 ^ 2011
  intro a ha
  -- It's clear that if `a>N` then `a` has at least `2012` digits.
  replace ha : 2012 ≤ (Nat.digits 10 a).length := calc
    _ = 2011 + 1 := by norm_num
    _ = Nat.log 10 (10 ^ 2011) + 1 := by congr 1; symm; apply Nat.log_pow; norm_num
    _ = (Nat.digits 10 (10 ^ 2011)).length := by rw [Nat.digits_len _ _ (by norm_num) (by positivity)]
    _ ≤ _ := by apply Nat.le_digits_len_le; linarith
  -- For (i=0, \ldots, 2011), let (b_{i}) be the number with decimal expansion
  -- (a_{i} a_{i-1} \ldots a_{0}).
  let b : Fin (Nat.digits 10 a).length → ℕ := fun k =>
    (∑ i ∈ Finset.range k, 10 ^ i * (Nat.digits 10 a)[i]!) % 2011
  -- Lemma for unfold `b k`.
  have hb_apply (k : Fin (Nat.digits 10 a).length) : b k =
    (∑ i ∈ Finset.range k, 10 ^ i * (Nat.digits 10 a)[i]!) % 2011 := rfl
  -- It follows that 2011 divides (b_{j} - b_{i} = c \cdot 10^{i}).
  -- Here (c) is the substring (a_{j} \ldots a_{i+1}).
  have key {i j : Fin (Nat.digits 10 a).length} (hij : i < j) (hb : b i = b j) :
      2011 ∣ ∑ k ∈ Finset.Ico i.val j.val, 10 ^ (k - i.val) * (Nat.digits 10 a)[k]!:= by
    -- Since 2011 and 10 are relatively prime, it follows that 2011 divides (c).
    have hco : Nat.Coprime 2011 (10 ^ i.val) := by apply Nat.Coprime.pow_right; norm_num
    apply Nat.Coprime.dvd_of_dvd_mul_left hco
    rw [Finset.mul_sum]
    simp [hb_apply] at hb
    change _ ≡ _ [MOD _] at hb
    rw [← Finset.sum_range_add_sum_Ico _ (show i.val ≤ j.val from hij.le)] at hb
    have {a b : ℕ} (h : a ≡ a + b [MOD 2011]) : b ≡ 0 [MOD 2011] := by
      exact Nat.ModEq.symm (Nat.ModEq.add_left_cancel (id (Nat.ModEq.symm h)) rfl)
    have := this hb
    rw [Nat.modEq_zero_iff_dvd] at this
    convert this using 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [← mul_assoc, ← pow_add]
    congr
    simp at hk
    omega
  -- Suffices to show that there exists `j,k` such that `b j  = b k` and `j ≠ k`.
  suffices ∃ j k : Fin (Nat.digits 10 a).length, b j = b k ∧ j ≠ k by
    rcases this with ⟨i, j, hb, hjk⟩
    rcases lt_trichotomy i j with h | h | h
    . use i, j
      refine ⟨h, by simp, ?_⟩
      exact key h hb
    . contradiction
    . use j, i
      refine ⟨h, by simp, ?_⟩
      exact key h hb.symm
  -- Then by the pigeonhole principle,
  -- (b_{i} \equiv b_{j} \bmod 2011) for some (i &lt; j \leq 2011).
  apply Function.not_injective_iff.mp
  intro hb
  have h1 : 2012 ≤ (Finset.univ.image b).card := le_trans ha
    (by simp [Finset.card_image_of_injective (Finset.univ) hb])
  suffices (Finset.univ.image b).card ≤ 2011 by linarith
  rw [← Finset.card_range 2011]
  apply Finset.card_le_card
  intro x hx
  simp at hx
  rcases hx with ⟨k, hk⟩
  simp
  rw [← hk, hb_apply]
  exact Nat.mod_lt _ (by norm_num)
