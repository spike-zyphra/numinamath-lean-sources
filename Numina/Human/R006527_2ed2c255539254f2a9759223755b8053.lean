import Mathlib

/-1. 1. Let $N_0$ be an integer satisfying $N_0 > 19$. Let $k_0$ be a positive integer such that
$k_0$ and $N_0$ are coprime (i.e., $\gcd(k_0, N_0)=1$). Let $R_0$ be the unique integer such that
$R_0 \equiv 19k_0 \pmod{N_0}$ and $0 \le R_0 < N_0$. Suppose $T$ is an integer period satisfying $0 < T < N_0$.
If $k_0 T \equiv R_0 \pmod{N_0}$, show that $T=19$.
-/

theorem number_theory_638065 (N k R T: ℤ) (h1: 19 < N) (h3: IsCoprime k N)
  (h4: R % N = (19 * k) % N) (h5: 0 < R) (h6: R < N) (h7: 0 < T) (h8: T < N)
  (h9: (k * T) % N = R % N) : T = 19 := by

  suffices T % N = 19 by
    rw [← this]
    symm
    apply Int.emod_eq_of_lt
    omega
    omega
  have u: R % N = R := by
    apply Int.emod_eq_of_lt
    omega
    omega
  simp [u] at *
  clear u
  rw [h4] at h9
  replace h9: (k * T - 19 * k) % N = 0 := by
    rw [Int.sub_emod]
    rw [h9]
    simp
  apply Int.dvd_of_emod_eq_zero at h9
  rw [show k * T - 19 * k = k * (T - 19) by
    ring] at h9
  apply IsCoprime.dvd_of_dvd_mul_left at h9
  .
    suffices (T - 19) % N = 0 by
      rw [show T = T - 19 + 19 by ring]
      rw [Int.add_emod]
      simp [this]
      apply Int.emod_eq_of_lt
      omega
      omega
    apply Int.emod_eq_zero_of_dvd
    tauto
  .
    apply IsCoprime.symm
    tauto