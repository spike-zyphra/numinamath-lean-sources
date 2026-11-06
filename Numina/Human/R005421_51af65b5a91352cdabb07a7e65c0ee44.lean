import Mathlib

open Finset Real ArithmeticFunction

/- Show that for positive integers $n$,

$$
\sum_{d \mid n} \frac{\mu(d)}{d}=\frac{\phi(n)}{n}
$$
-/
theorem number_theory_608228 {n : ℕ} (hn : 0 < n) :
  (∑ d ∈ n.divisors, moebius d / d : ℚ) = (n.totient : ℝ) / n :=
by
  let f (n : ℕ) : ℤ := n
  let g (n : ℕ) : ℤ := n.totient
  have : ∀ n > 0, ∑ i ∈ n.divisors, g i = f n := by
    simp [f, g]
    intro n h
    norm_cast
    apply Nat.sum_totient
  -- On the grounds of the previous problem, Möbius inversion with $f(k)=\phi(k)$ and $g(k)=k$ gives:
  have H := sum_eq_iff_sum_smul_moebius_eq.mp this n (by assumption)
  apply_fun (fun x => (x / n : ℚ)) at H
  push_cast at H
  rw [sum_div] at H
  simp [f, g] at H
  have : ∀ x ∈ n.divisorsAntidiagonal, x.2 = n / x.1 := by
    intro x h
    simp at h
    rcases h with ⟨h, h'⟩
    have : x.1 ≠ 0 := by
      intro g
      rw [g] at h
      simp at h
      tauto
    apply_fun (fun z => z / x.1) at h
    rw [mul_comm, Nat.mul_div_cancel] at h
    assumption
    . by_contra g
      simp at g
      tauto
  let F (a b : ℕ) : ℚ := (μ a) * ↑b / ↑n
  have : ∑ x ∈ n.divisorsAntidiagonal, ((μ x.1) * ↑x.2 / ↑n : ℚ) =
         ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2 := by simp [F]
  rw [this, Nat.sum_divisorsAntidiagonal] at H
  simp [F] at H
  -- $$ \phi(n)=f(n)=\sum_{d \mid n} g(d) \mu\left(\frac{n}{d}\right)=\sum_{d^{\prime} \mid n} g\left(\frac{n}{d^{\prime}}\right) \mu\left(d^{\prime}\right)=\sum_{d^{\prime} \mid n} \frac{n}{d^{\prime}} \mu\left(d^{\prime}\right) $$
  have : ∑ x ∈ n.divisors, ((μ x) * (n / x : ℕ) / n : ℚ) = ∑ x ∈ n.divisors, ((μ x) / x : ℚ) := by
    let F (x : ℕ) : ℚ := (μ x) * (n / x : ℕ) / n
    let G (x : ℕ) : ℚ := (μ x) / x
    have : ∀ x ∈ n.divisors, F x = G x := by
      intro x h
      simp at h
      simp [F,G]
      rcases h
      rw [Nat.cast_div]
      ring_nf
      rw [mul_assoc (μ x : ℚ), mul_assoc (μ x : ℚ)]
      congr
      rw [mul_comm, ←mul_assoc, inv_mul_cancel₀]
      simp
      norm_cast
      assumption
      simp
      apply ne_zero_of_dvd_ne_zero
      <;> assumption
    have := Finset.sum_congr (s₁ := n.divisors) (by rfl) this
    rw [this]
  rw [this] at H
  push_cast
  rify at H
  exact H
