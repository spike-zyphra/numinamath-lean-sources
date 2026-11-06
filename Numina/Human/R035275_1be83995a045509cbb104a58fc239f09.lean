import Mathlib

open Real

/- Soit $\left(u_{n}\right)_{n}$ une suite de réels telle que, pour tout entier $n$,

$$
\left|u_{n+1}-u_{n}\right| \leqslant 1 .
$$

Montrer que la moyenne des $n$ premiers termes de la suite et la moyenne des $n+1$ premiers termes de la suite sont distantes d'au plus $\frac{1}{2}$. -/
theorem inequalities_607468 (u : ℕ → ℝ) (h : ∀ n, |u (n + 1) - u n| ≤ 1) :
    ∀ n ≥ 1, |(∑ i in Finset.range (n + 1), u i) / (n + 1) - (∑ i in Finset.range n, u i) / n| ≤ 1 / 2 := by
  -- Notons, pour tout entier $n$ strictement positif $v_{n}=\frac{1}{n}\left(u_{1}+\ldots+u_{n}\right)$. $\triangleright$ Soit $\mathrm{m}&gt;\mathrm{n}$.
  obtain ⟨v, hv⟩ := show ∃v : ℕ → ℝ, (∀n, v n = (∑ i in Finset.range n, u i) / n) by
    use λn ↦ (∑ i in Finset.range n, u i) / n; simp
  intro n hn
  have := hv (n + 1)
  simp at this
  rw [←hv n, ←this]

  -- Remarquons tout d'abord que, par inégalité triangulaire, $$ \begin{aligned} \left|u_{m}-u_{n}\right| & \leqslant\left|u_{m}-u_{m-1}\right|+\left|u_{m-1}-u_{m-2}\right|+\ldots+\left|u_{n+1}-u_{n}\right| \ & \leqslant m-n . \end{aligned} $$
  have _lemma (n : ℕ) (m : ℕ) (h' : n < m) : |u m - u n| ≤ m - n := by
    have h₂ (x : ℕ) (hx : x ≤ m - n) : |u (x + n) - u n| ≤ x := by
      induction' x using Nat.strongRec with x ih
      by_cases hx' : x = 0
      · rw [hx']
        simp
      specialize ih (x - 1) (by omega) (by omega)
      have : |u (x + n) - u n| ≤ |u (x + n) - u (x + n - 1)| + |u (x - 1 + n) - u n| := by
        rw [show x - 1 + n = x + n - 1 by omega]
        exact abs_sub_le (u (x + n)) (u (x + n - 1)) (u n)
      apply le_trans this
      have : |u (x + n) - u (x + n - 1)| ≤ 1 := by
        specialize h (x + n - 1)
        rw [Nat.sub_add_cancel] at h
        exact h
        omega
      apply le_trans (add_le_add this ih)
      norm_cast
      omega
    specialize h₂ (m - n) (by omega)
    rw [show m - n + n = m by omega, Nat.cast_sub] at h₂
    exact h₂
    linarith

  -- $\triangleright$ Pour tout entier n strictement positif,
  -- $$ \begin{aligned} \left|v_{n+1}-v_{n}\right| & =\left|\frac{(n+1)\left(u_{1}+\ldots+u_{n}\right)-n\left(u_{1}+\ldots+u_{n}+u_{n+1}\right)}{n(n+1)}\right| \ & \leqslant\left|\frac{\left(u_{1}-u_{n+1}\right)+\ldots+\left(u_{n}-u_{n+1}\right)}{n(n+1)}\right| \ & \leqslant \frac{\left|u_{1}-u_{n+1}\right|+\ldots+\left|u_{n}-u_{n+1}\right|}{n(n+1)} \ & \leqslant \frac{n+\ldots+1}{n(n+1)}=\frac{1}{2} \end{aligned} $$
  have : |v (n + 1) - v n| ≤ |(∑ i ∈ Finset.range n, (u i - u n)) / ((n + 1) * n)| := by
    rw [abs_div, le_div_iff₀, ←abs_mul, hv, hv, sub_mul, div_mul, div_mul, ←div_div]; simp
    rw [div_self, ←div_mul, div_one, ←div_div, div_right_comm, div_self, ←div_mul, div_one, abs_sub_comm]
    rw [Finset.range_succ, mul_add]
    simp; ring_nf; simp
    norm_cast
    linarith
    norm_cast
    norm_cast
    simp
    linarith

  apply le_trans this
  rw [abs_div, abs_mul, show |(n + 1 : ℝ)| = n + 1 by rw [abs_eq_self]; positivity, show |(n : ℝ)| = n by rw [abs_eq_self]; positivity]

  apply (div_le_iff₀' (by norm_cast; simp; positivity)).mpr
  have : (n + 1 : ℝ) * n * (1 / 2) = ∑ i in Finset.range n, (i + 1) := by
    -- apply Finset.sum_range_id
    rw [Finset.sum_add_distrib, Finset.sum_range_id, Finset.sum_const]
    field_simp
    have : (n * (n - 1) / 2 : ℕ) * (2 : ℝ) = n * n - n := by
      norm_cast
      rw [Nat.div_mul_cancel, Nat.mul_sub, mul_one, Nat.cast_sub (Nat.le_mul_self n)]
      simp
      apply (Nat.Prime.dvd_mul (by norm_num)).mpr
      by_cases h: Even (n - 1)
      · exact even_iff_two_dvd.mp h |> Or.inr
      simp at h
      have : Even n := by
        rw [←Nat.sub_add_cancel (show 1 ≤ n by omega)]
        exact Odd.add_one h
      exact even_iff_two_dvd.mp this |> Or.inl
    rw [add_mul, add_mul, this]
    ring_nf
  rw [this]
  apply le_trans
  apply Finset.abs_sum_le_sum_abs
  simp
  have : ∑ x ∈ Finset.range n, (x + 1 : ℝ) = ∑ x in Finset.range n, (n - x : ℝ) := by
    simp
    rw [Finset.sum_add_distrib, ←Nat.cast_sum, Finset.sum_range_id, Finset.sum_const]
    simp
    have : (n * (n - 1) / 2 : ℕ) * (2 : ℝ) = n * n - n := by
      norm_cast
      rw [Nat.div_mul_cancel, Nat.mul_sub, mul_one, Nat.cast_sub (Nat.le_mul_self n)]
      simp
      apply (Nat.Prime.dvd_mul (by norm_num)).mpr
      by_cases h: Even (n - 1)
      · exact even_iff_two_dvd.mp h |> Or.inr
      simp at h
      have : Even n := by
        rw [←Nat.sub_add_cancel (show 1 ≤ n by omega)]
        exact Odd.add_one h
      exact even_iff_two_dvd.mp this |> Or.inl
    rw [eq_sub_iff_add_eq, add_comm, ←add_assoc, ←mul_two, this]
    ring_nf
  rw [this]
  apply Finset.sum_le_sum
  simp
  intro i hi
  rw [abs_sub_comm]
  exact _lemma i n hi
