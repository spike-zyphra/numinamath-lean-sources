import Mathlib

/- Soit $n$ un entier vérifiant $n \geqslant 2$. On note $d$ le plus grand diviseur de $n$ différent de $n$. On suppose que $\mathrm{d}>1$. Démontrer que $\mathrm{n}+\mathrm{d}$ n'est pas une puissance de 2 . -/
theorem number_theory_607175 {n d: ℕ} (hn : 2 ≤ n) (hd : d ∣ n) (hdn : d ≠ n)
  (hm : ∀ k, d < k → k ∣ n → k = n) (h₁ : d > 1) :
  ¬∃ k, n + d = 2 ^ k := by
    intro ⟨r, hr⟩
    -- Supposons par l'absurde que $n+d$ est une puissance de 2 . Notons que $d$ divise $n$, donc $d$ divise $n+d$, donc $d$ divise une puissance de 2 . Ainsi $d$ est une puissance de $2:$ on pose $d=2^{k}$ pour un certain $k \in \mathbb{N}$.
    have h1 : d ∣ 2^r := hr ▸ Nat.dvd_add hd (show d ∣ d by rfl)
    obtain ⟨k, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    --  On a $k \geqslant 1$ car $d \neq 1$.
    have hk' : 1 ≤ k := by
      by_contra!
      have : k = 0 := by omega
      simp [this] at hk
      omega
    rw [hk.2] at hd
    obtain ⟨a, ha⟩ := hd
    -- Posons $n=d a=2^{k} a$ avec $a \in \mathbb{N}^{\*}$. Comme $d$ est différent de $n$, on a $a \geqslant 2$.
    have age2 : 2 ≤ a := by
      by_contra! alt2
      interval_cases a <;> omega
    have h2 : 2^(k - 1) * a ∣ n := by
      simp [ha]; refine Nat.mul_dvd_mul (pow_dvd_pow 2 (by omega)) (by rfl)
    -- Ainsi $2^{k-1} a$ est un diviseur de $n$, supérieur ou égal à $2^{k}=d$, et différent de $n$. Par hypothèse $d=2^{k-1} a$, donc $a=2$.
    have a2 : a = 2 := by
      by_contra!
      have agt2 : 2 < a := by omega
      have h3 : d < 2^(k - 1) * a := by
        simp [hk.2]
        nth_rw 1 [show k = k - 1 + 1 from (Nat.sub_add_cancel hk').symm, pow_add]
        apply mul_lt_mul' (by rfl) agt2 (by omega) (by positivity)
      have h4 := hm (2^(k-1) * a) h3 h2
      simp [ha] at h4
      rcases h4 with h4 | h4 <;> omega
    -- Ainsi $n=2^{k+1}$. On trouve alors $\mathrm{n}+\mathrm{d}=2^{\mathrm{k}}(2+1)=3 \times 2^{\mathrm{k}}$ qui n'est pas une puissance de 2 , ce qui est une contradiction. 
    have h5 : n + d = 2^k * 3 := calc
      _ = 2^k * 2 + 2^k := by rw [ha, hk.2, a2]
      _ = _ := by rw [show 3 = 2 + 1 by rfl, mul_add, mul_one]
    rw [h5] at hr
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three <| hr ▸ (Nat.dvd_mul_left 3 _)
    omega
