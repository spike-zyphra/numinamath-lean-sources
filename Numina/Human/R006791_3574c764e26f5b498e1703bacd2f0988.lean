import Mathlib

/-"Let $k$ be a non-zero digit (i.e., $k \in \{1, 2, \dots, 9\}$). In a parlor game,
a participant thinks of a three-digit number $(abc)$ where $a,b,c$ are digits in base 10 and $a \ne 0$.
The magician asks the participant to form the numbers $(acb)$, $(bca)$, $(bac)$, $(cab)$, and $(cba)$,
add these five numbers, and reveal their sum. Suppose the participant chose the number $(kkk)$ (meaning $a=b=c=k$).
The sum of the five specified permutations is $N_k = 122k + 212k + 221k = 555k$.
Play the role of the magician: if the revealed sum is $N_k = 555k$,
determine the original number $(abc)$. Show that the original number $(abc)$ is $111k$."
-/

theorem number_theory_641175 (a b c k: ℤ) (la: 1 ≤ a) (ra: a ≤ 9) (lb: 0 < b) (rb: b ≤ 9) (lc: 0 < c) (rc: c ≤ 9)
  (h: (100 * a + 10 * c + b) + (100 * b + 10 * c + a) + (100 * b + 10 * a + c) + (100 * c + 10 * a + b) + (100 * c + 10 * b + a)
  = 555 * k): 100 * a + 10 * b + c = 111 * k := by
    ring_nf at h
    rw [show a * 122 + c * 221 + b * 212 = 222 * (a + b + c) - (100 * a + 10 * b + c) by ring] at h
    set n:= 100 * a + 10 * b + c
    have d: 111 ∣ n := by
      rw [show n = 111 * (2 * a + 2 * b + 2 * c - k * 5) by nlinarith]
      simp
    apply exists_eq_mul_right_of_dvd at d
    obtain ⟨s, hs⟩ := d
    simp [hs] at h
    replace h: 2 * (a + b + c) = s + 5 * k := by omega
    omega
