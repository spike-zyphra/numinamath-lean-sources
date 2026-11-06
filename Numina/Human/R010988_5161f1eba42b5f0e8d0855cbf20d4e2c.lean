import Mathlib

open Real Set
/--
Problem statement (Main theorem of this file):
Task B-3.1. Solve the equation

$$
\log _{\sqrt{2} \sin x}(1+\cos x)=2
$$

Solution:
Rješenje. Jednadžba ima smisla jedino ako je $1+\cos x > 0$, odnosno ako je $\cos x > -1$, a to znači za sve $x \in \mathbb{R}$ osim kada je $\cos x=-1$.

(1 bod)

Isto tako baza logaritamske funkcije mora biti pozitivna i različita od 1 pa vrijedi $\sqrt{2} \sin x > 0$ i $\sqrt{2} \sin x \neq 1$, odnosno

$$ \sin x > 0 \quad \text { i } \quad \sin x \neq \frac{1}{\sqrt{2}} $$

Iz same jednadžbe slijedi

$$ \begin{aligned} 1+\cos x & =2 \sin ^{2} x \\ 1+\cos x & =2\left(1-\cos ^{2} x\right) \\ 2 \cos ^{2} x+\cos x-1 & =0 \end{aligned} $$

te dobivamo $\cos x=\frac{1}{2} \mathrm{i} \cos x=-1$.

(1 bod)

$\cos x=-1$ nije rješenje zbog početnog uvjeta, a iz $\cos x=\frac{1}{2}$ dobivamo $x=\frac{\pi}{3}+2 k \pi$ ili $x=-\frac{\pi}{3}+2 k \pi$. Zbog početnog uvjeta rješenje je samo $x=\frac{\pi}{3}+2 k \pi$.

(1 bod)

-/

lemma cos_eq_one_div_two (x : ℝ) (h : cos x = 1 / 2) :
    ∃ k : ℤ, x = π / 3 + 2 * k * π ∨ x = -π / 3 + 2 * k * π := by
    rw [← cos_pi_div_three, cos_eq_cos_iff] at h
    rcases h with ⟨k, h⟩
    cases' h with h1 h2
    . use -k
      left
      rw [h1]
      ring_nf
      simp
      ring_nf
    . use k
      right
      rw [(by ring: -π / 3 = -(π / 3))]
      rw [h2]
      ring_nf

theorem algebra_214233 (x : ℝ):
    (1 + cos x) > 0 → (sqrt 2 * sin x) > 0 → (sqrt 2 * sin x) ≠ 1 → (logb (sqrt 2 * sin x) (1 + cos x) = 2 ↔ (∃ k : ℤ, x = π / 3 + 2 * k * π )) := by
    intro h_pos h_base_pos h_base_neq_1
    constructor
    . intro h_log
      rw [logb_eq_iff_rpow_eq h_base_pos h_base_neq_1 h_pos] at h_log
      norm_cast at h_log
      ring_nf at h_log
      field_simp at h_log
      rw [sin_sq] at h_log
      have : cos x = 1 / 2:= by
        rw [(by ring : (1 - cos x ^ 2) = (1 - cos x) * (1 + cos x)), ← mul_assoc] at h_log
        have : 1 + cos x ≠ 0 := by positivity
        field_simp at h_log
        linarith

      apply cos_eq_one_div_two x at this
      rcases this with ⟨k, hx⟩
      cases' hx with hx1 hx2
      . use k
      . have h_sin : sin x = - √3 / 2 := by
          rw [hx2]
          rw [(by ring : 2 * k * π = k * (2 * π))]
          rw [sin_add_int_mul_two_pi (-π / 3) k]
          rw [(by ring : -π / 3 = -(π / 3))]
          rw [sin_neg, sin_pi_div_three]
          ring_nf

        have : sqrt 2 > 0 := by positivity
        have : sin x > 0 := by
          apply (mul_pos_iff_of_pos_left this).mp
          exact h_base_pos
        have : sin x < 0 := by rw [h_sin]; ring_nf; norm_num
        linarith

    . intro h_exists
      rcases h_exists with ⟨k, hx⟩
      rw [(by ring : 2 * k * π = k * (2 * π))] at hx
      rw [hx]
      rw [sin_add_int_mul_two_pi (π / 3) k]
      rw [cos_add_int_mul_two_pi (π / 3) k]
      rw [sin_pi_div_three]
      rw [cos_pi_div_three]
      rw [logb_eq_iff_rpow_eq (by positivity) (by aesop) (by positivity)]
      simp
      ring_nf
      norm_num
