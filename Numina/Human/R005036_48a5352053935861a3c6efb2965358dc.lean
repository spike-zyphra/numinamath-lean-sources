import Mathlib

/- Gegeven is een onbekende rij $a_{1}, a_{2}, a_{3}, \ldots$ van gehele getallen die voldoet aan de volgende eigenschap: voor elk priemgetal $p$ en elk positief geheel getal $k$ geldt

$$
a_{p k+1}=p a_{k}-3 a_{p}+13
$$

Bepaal alle mogelijke waarden van $a_{2013}$. -/
theorem number_theory_605170 (a : ℕ → ℤ) (h : ∀ p k, Nat.Prime p → k > 0 → a (p * k + 1) = p * a k - 3 * a p + 13) :
    a 2013 = 2016 := by

    -- For primes q t, we have (t+3) * a q = (q+3) * a t, which follows from assumption h.
    have lemeq (q t : ℕ) (hq: Nat.Prime q) (ht: Nat.Prime t) :
    (t+3) * a q = (q+3) * a t := by
        have qpos : 0<q := by exact Nat.Prime.pos hq
        have tpos : 0<t := by exact Nat.Prime.pos ht
        have tmp1: a (t*q+1) = t*a q - 3 * a t + 13 := by
            apply h t q; assumption; assumption
        have tmp2: a (q*t+1) = q*a t - 3 * a q + 13 := by
            apply h q t; assumption; assumption
        have tmp3: a (t*q+1) = a (q*t+1) := by ring_nf
        have : t*a q - 3 * a t + 13 = q*a t - 3 * a q + 13 := by
            rw [← tmp1]; rw [← tmp2]; assumption
        simp at this; linarith

    -- using the previous lemma, we get a 2 = 5
    have ha2 : a 2 = 5 := by
        have : 5 * a 3 = 6 * a 2 := by
            apply lemeq 3 2; norm_num; norm_num
        have : 5 * a 7 = 10* a 2 := by
            apply lemeq 7 2; norm_num; norm_num
        have : a 7 = 2 * a 3 - 3 * a 2 + 13 := by apply h 2 3; norm_num; linarith
        omega
    -- plugging a 2 = 5 in the previous lemma, we have that for every prime p, a p = p + 3.
    have lempri (p : ℕ) (hp : Nat.Prime p) : a p = p + 3 := by
        have : (2+3) * a p = (p+3) * a 2 := by
            apply lemeq p 2
            exact hp; norm_num
        simp [ha2] at this; linarith

    -- The remaining part is to use the assumption h and the lemma to decompose 2013 and verify that a 2013 equal 2016
    have ha4 : a 4 = 7 := by
        have ha13 : a 13 = 16 := by apply lempri 13; norm_num
        have ha3  : a 3 = 6 := by apply lempri 3; norm_num
        have : a 13 = 3 * a 4 - 3 * a 3 + 13 := by
            apply h 3 4; norm_num; linarith
        omega

    have pri503 : Nat.Prime 503 := by norm_num
    have ha503 : a 503 = 506 := by apply lempri; assumption

    have tmp : a 2013 = 503 * a 4 - 3 * a 503 + 13 := by
        apply h 503 4; assumption; linarith

    omega
