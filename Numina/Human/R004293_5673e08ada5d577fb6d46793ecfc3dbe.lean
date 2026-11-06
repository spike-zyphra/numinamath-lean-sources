import Mathlib

open Finset

/- # Problem:
 ## Task 4.

For a natural number, we say it is unusual if the sum of the reciprocals of all its positive divisors is different from the sum of the reciprocals of all positive divisors of any other natural number.

(a) Prove that all prime numbers are unusual.

(b) Prove that there are infinitely many natural numbers that are not unusual.
## Rješenje.

Označimo s $r(n)$ zbroj recipročnih vrijednosti, a sa $\sigma(n)$ zbroj svih pozitivnih djelitelja broja $n$. Očito vrijedi $r(n) > 1$ za $n > 1$. Za svaki djelitelj $d$ broja $n$ i broj $\frac{n}{d}$ je djeljitelj od $n$, pa vrijedi

$$ r(n)=\sum_{d \mid n} \frac{1}{d}=\sum_{d \mid n} \frac{d}{n}=\frac{\sigma(n)}{n} $$

Ako su $a$ i $b$ relativno prosti brojevi, onda vrijedi $\sigma(a b)=\sigma(a) \sigma(b)$. Zaista, $d$ je pozitivni djelitelj broja $a b$ ako i samo ako se može prikazati u obliku $d=d^{\prime} d^{\prime \prime}$ pri čemu je $d^{\prime}$ pozitivni djelitelj od $a$ i $d^{\prime \prime}$ pozitivni djelitelj od $b$. Budući da su $a$ i $b$ relativno prosti, $d^{\prime}$ i $d^{\prime \prime}$ su jedinstveno određeni. Zato je

$$ \sigma(a b)=\sum_{d \mid a b} d=\sum_{d^{\prime}\left|a, d^{\prime \prime}\right| b} d^{\prime} d^{\prime \prime}=\left(\sum_{d^{\prime} \mid a} d^{\prime}\right) \cdot\left(\sum_{d^{\prime \prime} \mid a} d^{\prime \prime}\right)=\sigma(a) \sigma(b) $$

Također zaključujemo da je

$$ r(a b)=\frac{\sigma(a b)}{a b}=\frac{\sigma(a) \sigma(b)}{a b}=r(a) r(b) $$

(a) Neka je $n$ prost broj i pretpostavimo da postoji $m \neq n$ takav da je $r(n)=r(m)$. Tada je

$$ \frac{1}{n}=r(n)-1=r(m)-1=\frac{\sigma(m)}{m}-1=\frac{\sigma(m)-m}{m} $$

iz čega slijedi $m=n(\sigma(m)-m)$, tj. $n$ dijeli $m$. Budući da je $m \neq n$, slijedi da je

$$ r(m) \geqslant 1+\frac{1}{n}+\frac{1}{m}=r(n)+\frac{1}{m} > r(n) $$

što je kontradikcija.

(b) Ako nađemo bilo koja dva različita prirodna broja $m$ i $n$ takva da je $r(m)=r(n)$, onda i za svaki $k$ relativno prost s $n m$ vrijedi $r(m k)=r(n k)$.

Jedan takav par su brojevi 6 i 28 jer je

$$ r(6)=\frac{1+2+3+6}{6}=2=\frac{1+2+4+7+14+28}{28}=r(28) $$

Dakle, nisu neobični svi brojevi oblika $6 p$, pri čemu je $p$ prost broj strogo veći od 7. Takvih brojeva ima beskonačno mnogo.

## Drugi test

## 20. lipnja 2020. -/


def r (n : ℕ) : ℚ := ∑ d ∈ n.divisors, (1 / d)

def isUnusual (n : ℕ) := ∀ m, m ≠ n → r m ≠ r n

lemma r_eq_sigma_div_n {n : ℕ} (hn: n ≠ 0) : r n = (n.divisors.sum id) / n := by
  unfold r

  have := Nat.sum_div_divisors n (fun d => 1 / (d:ℚ))
  rw [← this]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have : d ≠ 0 := by
    by_contra
    subst d
    simp at hd
  have : n/d ≠ 0 := by
    by_contra h
    simp at h
    rcases h with (h | h)
    . contradiction
    . contrapose h
      simp
      simp at hd
      apply Nat.le_of_dvd
      . omega
      . exact hd.1


  field_simp
  norm_cast
  rw [Nat.mul_div_cancel']
  simp at hd
  exact hd.1

lemma r_mul {a b : ℕ} (h : Nat.Coprime a b) : r (a * b) = r a * r b := by
  by_cases ha : a = 0
  . subst a
    simp
    rw [show r 0 = 0 by native_decide]
    simp
  . by_cases hb : b = 0
    . subst b
      simp
      rw [show r 0 = 0 by native_decide]
      simp
    . rw [r_eq_sigma_div_n hb]
      rw [r_eq_sigma_div_n ha]
      rw [r_eq_sigma_div_n (show a * b ≠ 0 by simp; omega)]
      field_simp
      rw [show ∑ x ∈ (a * b).divisors, (x:ℚ) = ∑ x ∈ (a * b).divisors, x by simp]
      rw [show ∑ x ∈ a.divisors, (x:ℚ) = ∑ x ∈ a.divisors, x by simp]
      rw [show ∑ x ∈ b.divisors, (x:ℚ) = ∑ x ∈ b.divisors, x by simp]
      have := Nat.Coprime.sum_divisors_mul h
      rw [this]
      simp


lemma coprime_6_p (p : ℕ) (hp3 : Nat.Prime p) (hp2 : 8 ≤ p) :
    Nat.Coprime 6 p := by
  have h1 : p % 2 ≠ 0 := by
    by_contra h
    have h2 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals omega
    contradiction
  have h2 : p % 3 ≠ 0 := by
    by_contra h
    have h3 : 3 ∣ p := by omega
    have h4 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals omega
    contradiction
  -- Now, to show that 6 and p are coprime.
  -- Since p is neither divisible by 2 nor by 3, then gcd(6, p) = 1.
  rw [Nat.coprime_iff_gcd_eq_one]
  have h6 : Nat.gcd 6 p = 1 := by
    have h7 : Nat.gcd 6 p ∣ 6 := by
      exact Nat.gcd_dvd_left 6 p
    have h8 : Nat.gcd 6 p ∣ p := by
      exact Nat.gcd_dvd_right 6 p
    have h9 : Nat.gcd 6 p ≤ 6 := by
      exact Nat.le_of_dvd (by norm_num) h7
    interval_cases k : Nat.gcd 6 p <;> try {
      omega
    }
  exact h6

lemma coprime_28_p (p : ℕ) (hp3 : Nat.Prime p) (hp2 : 8 ≤ p) :
    Nat.Coprime 28 p := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have h4 : Nat.gcd 28 p ∣ 28 := by
    exact Nat.gcd_dvd_left 28 p
  have h5 : Nat.gcd 28 p ∣ p := by
    exact Nat.gcd_dvd_right 28 p
  have h6 : Nat.gcd 28 p = 1 := by
    have h9 : Nat.gcd 28 p = 1 ∨ Nat.gcd 28 p = p := by
      have h10 : Nat.gcd 28 p ∣ p := h5
      have h11 : Nat.gcd 28 p = 1 ∨ Nat.gcd 28 p = p := by
        apply (Nat.dvd_prime hp3).mp at h10
        omega
      tauto
    rcases h9 with (h | h)
    · tauto
    · -- Case where gcd(28, p) = p
      have h10 : p ∣ 28 := by
        have h11 : Nat.gcd 28 p ∣ 28 := h4
        rw [show Nat.gcd 28 p = p by linarith] at h11
        omega
      have h11 : p ≤ 28 := Nat.le_of_dvd (by norm_num) h10
      interval_cases p <;> norm_num at hp3 h10 h11 hp2
  rw [h6]

theorem number_theory_249280 :
  (∀ p, Nat.Prime p → isUnusual p) ∧
  {n | ¬ isUnusual n}.Infinite := by

  split_ands
  . intro p hp
    unfold isUnusual
    intro m hm
    by_contra hc
    have hp_ne_zero : p ≠ 0 := by
      contrapose hp
      simp at hp
      subst p
      decide

    have hm_ne_zero : m ≠ 0 := by
      by_contra h
      subst m
      rw [show r 0 = 0 by native_decide] at hc
      unfold r at hc
      rw [Nat.Prime.sum_divisors hp] at hc
      field_simp at hc
      norm_cast at hc
      omega

    have h1: m = p * m.properDivisors.sum id := by
      rw [r_eq_sigma_div_n hm_ne_zero] at hc
      unfold r at hc
      rw [Nat.Prime.sum_divisors hp] at hc
      field_simp at hc
      have : (∑ x ∈ m.divisors, (x:ℚ)) = (∑ x ∈ m.divisors, x) := by
        simp

      rw [this] at hc
      norm_cast at hc
      simp

      rw [← Nat.insert_self_properDivisors hm_ne_zero] at hc
      rw [Finset.sum_insert Nat.properDivisors.not_self_mem] at hc
      linarith

    have h2: {1,p,m} ⊆ m.divisors := by
      intro x hx
      simp at hx
      simp
      split_ands
      . rcases hx with rfl | rfl | rfl
        . simp
        . use m.properDivisors.sum id
        . simp
      . assumption

    have h3: ∑ d ∈ ({1,p,m} : Finset ℕ), (1/(d:ℚ))  ≤ ∑ d ∈ m.divisors, (1/(d:ℚ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      . exact h2
      . intro d hd1 hd2
        simp

    have h4 : ∑ d ∈ ({1,p,m} : Finset ℕ), (1/(d:ℚ)) = 1 + 1/p + 1/m := by
      simp
      rw [Finset.sum_insert]
      rw [Finset.sum_pair]
      ring
      . omega
      . simp
        split_ands
        . contrapose hp
          simp at hp
          subst p
          decide
        . by_contra
          subst m
          simp at h1

    rw [h4] at h3
    unfold r at hc
    rw [hc] at h3
    rw [Nat.Prime.sum_divisors hp] at h3
    have : 1/(m:ℚ) > 0 := by simp; omega
    linarith

  . rw [Set.infinite_iff_exists_gt]
    intro a

    have ⟨p, hp, hp3⟩ := Nat.exists_infinite_primes (max a 8)
    simp at hp
    obtain ⟨hp1, hp2⟩ := hp
    use 6*p
    refine ⟨?_, by linarith⟩
    unfold isUnusual
    simp
    use 28*p
    split_ands
    . simp
      contrapose hp3
      simp at hp3
      subst p
      decide
    . rw [r_mul]
      rw [r_mul]
      have : r 28 = r 6 := by native_decide

      rw [this]
      . apply coprime_6_p
        all_goals assumption
      . apply coprime_28_p
        all_goals assumption
