import Mathlib

/- # Problem:
 Exercise 4. a) Find a strictly positive integer $n$ such that if we write $n^{2}$ and remove the last two digits, the resulting number is still the square of an integer.

b) Find all strictly positive integers $n$ that are not multiples of 10 such that when writing $n^{2}$ and removing the last two digits, the resulting number is still the square of an integer (we consider a number with zero digits to be zero).
Solution de de'exercice 4 a) Tout multiple de 10 convient. En effet, un multiple de 10 strictement positif peut s'écrire $10 k, k \in \mathbb{N}^{*}$. Alors son carré vaut $100 k^{2}$, et si on retire les deux derniers chiffres de son écriture, qui sont des zéros, on obtient $\mathrm{k}^{2}$, qui est bien un carré parfait.

b) Si n est strictement inférieur à 10 , son carré a au au deux chiffres, donc en les retirant, on obtient zéro d'après la convention de l'énoncé. Si $n$ vérifie la propriété sans être multiple de $10, n^{2}$ n'est pas multiple de 100 . Soit $d$ le nombre tel que $d^{2}$ soit égal à $n^{2}$ privé de ses deux derniers chiffres. Alors $n^{2}$ et $(10 \mathrm{\~d})^{2}$ sont des carrés parfaits distincts dont la différence vaut au plus 99: car l'écriture $(10 \mathrm{\~d})^{2}$ s'obtient $^{2}$ en remplaçant les deux derniers chiffres de celle de $n^{2}$ par des zéros. Comme $(10 \mathrm{\~d})^{2} < \mathrm{n}^{2}$, on a $10 \mathrm{\~d} < \mathrm{n}$. Or $10 \mathrm{\~d}$ et $n$ sont entiers, donc $n \geqslant 10 \mathrm{\~d}+1$, donc $\mathrm{n}^{2} \geqslant(10 \mathrm{\~d})^{2}+2 \times 10 \mathrm{\~d}+1$. Or $\mathrm{n}^{2} \leqslant(10 \mathrm{\~d})^{2}+99$ donc $10 \mathrm{\~d} \leqslant 48$. Comme $\mathrm{d}$ est entier, $\mathrm{d} \leqslant 4$, ainsi $10 \mathrm{\~d} \leqslant 40$ et $(10 \mathrm{\~d})^{2} \leqslant 1600$. Ainsi, $\mathrm{n}^{2} \leqslant 1699$, soit $\mathrm{n} \leqslant 41$ comme $n$ est entier. Si le dernier chiffre de $n$ n'est pas $1, n \geqslant 10 d+2$ donc $n^{2} \geqslant(10 d)^{2}+40 d+4$ et on trouve $d \leqslant 2$. Si le dernier chiffre de $n$ n'est $n i 1 n i n \geqslant 10 d+3$ et on trouve de même $d \leqslant 1$. Si ce n'est ni 1 , ni 2 , ni 3 , ni $4, n \geqslant 10 d+5$ et on trouve $d=0$. Ainsi, il faut encore tester $11,12,13,14,21,22,31\ et 41 dont on vérifie rapidement qu'ils sont solutions, en plus de $1,2,3,4,5,6,7,8$ et 9 . -/
theorem number_theory_294332 :
  (∀ n : ℕ, n = 10 → IsSquare ((n^2) / 100)) ∧
  {n | (¬ 10 ∣ n) ∧ IsSquare ((n^2) / 100)} = {1,2,3,4,5,6,7,8,9,11,12,13,14,21,22,31,41} := by

  constructor
  . intro n h
    subst n
    decide
  . ext n
    simp
    constructor
    . intro ⟨h1, h2⟩
      by_cases hn1 : n < 10
      . interval_cases n
        all_goals simp
        simp at h1
      . have ⟨k, hk⟩ := h2
        rw [← pow_two] at hk
        have : 100 * k^2 ≤ n^2 := by omega
        have : n^2 ≤ 100 * k^2 + 99 := by omega
        have : 10*k ≤ n := by nlinarith
        have : 10*k + 1 ≤ n := by omega
        have : 20*k + 1 ≤ 99 := by nlinarith
        have : k ≤ 4 := by omega
        have : n ≤ 41 := by nlinarith
        interval_cases n
        all_goals simp
        all_goals contrapose h1; try native_decide
        all_goals contrapose h2; native_decide

    . rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals simp
      all_goals native_decide
