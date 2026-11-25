# Proof of A356976, Conjecture 2

**Status:** `proof (formalized)` — fully formalized and kernel-verified in pure Lean 4 v4.36.0 ([`A356976Conj2.lean`](A356976Conj2.lean), zero external dependencies, zero `sorry`, standard axioms `[propext, Classical.choice, Quot.sound]`).

## Statement (A356976, Conjecture 2)

> **Theorem.** Let $f(k) = 2k^3 + k$. For every positive integer $n$, the least positive integer $m$ such that $f(1), f(2), \dots, f(n)$ are pairwise distinct modulo $m$ is $2^{\lceil \log_2 n \rceil}$ (the least power of $2$ not smaller than $n$).

Equivalently, let $D_f(n)$ denote this least modulus. We prove $D_f(n) = 2^{\lceil \log_2 n \rceil}$ for all $n \ge 1$.

---

## 1. Upper bound: $D_f(n) \le 2^{\lceil \log_2 n \rceil}$

**Lemma 1.** *For every integer $r \ge 0$, the map $k \mapsto f(k) = 2k^3 + k$ is a bijection on $\mathbb{Z}/2^r\mathbb{Z}$.*

*Proof.* For any integers $x, y$,
$$f(y) - f(x) = (y - x)\bigl(2(x^2 + xy + y^2) + 1\bigr).$$
Since $2(x^2 + xy + y^2) + 1$ is odd, we have $2^r \mid (f(y) - f(x))$ if and only if $2^r \mid (y - x)$. Hence $f$ is injective (and therefore bijective) on $\mathbb{Z}/2^r\mathbb{Z}$. $\square$

Taking $m = 2^{\lceil \log_2 n \rceil} \ge n$, the values $f(1), \dots, f(n)$ are pairwise distinct modulo $m$, so $D_f(n) \le 2^{\lceil \log_2 n \rceil}$.

---

## 2. Reduction of the lower bound

To prove $D_f(n) = 2^{\lceil \log_2 n \rceil}$ for all $n \ge 1$, it is necessary and sufficient to show that for every positive integer $m$ that is **not** a power of $2$, $f(1), \dots, f(n)$ are *not* pairwise distinct modulo $m$ whenever $n > 2^{\lfloor \log_2 m \rfloor}$. Equivalently:

> **Target Claim.** For every positive integer $m$ that is not a power of $2$, there exist integers $1 \le x < y \le 2^{\lfloor \log_2 m \rfloor} + 1$ such that $f(x) \equiv f(y) \pmod m$.

Note that if $2^r < m < 2^{r+1}$, then $m \le 2^{r+1} - 1$, so $2^r \ge \frac{m+1}{2} > \frac{m}{2}$. Thus any pair $1 \le x < y \le \lfloor m/2 \rfloor + 1$ automatically satisfies $y \le 2^{\lfloor \log_2 m \rfloor} + 1$.

---

## 3. Case 1: $3 \mid m$

Write $m = 3^e d'$ with $e \ge 1$ and $3 \nmid d'$. For every integer $k$, $f(k) = 2k^3 + k \equiv 2k + k = 3k \equiv 0 \pmod 3$, so $f(k) \bmod 3^e$ always lies in $3\mathbb{Z}/3^e\mathbb{Z}$, a set of size $3^{e-1}$.

Consider the $3^{e-1} + 1$ integers $k_j = 1 + j d'$ for $j = 0, 1, \dots, 3^{e-1}$. By the pigeonhole principle, there exist $0 \le i < j \le 3^{e-1}$ such that $f(k_i) \equiv f(k_j) \pmod{3^e}$. Since $d' \mid (k_j - k_i)$, we also have $f(k_i) \equiv f(k_j) \pmod{d'}$. Because $\gcd(3^e, d') = 1$, it follows that $f(k_i) \equiv f(k_j) \pmod{m}$. Finally,
$$1 \le k_i < k_j \le 1 + 3^{e-1} d' = 1 + \frac{m}{3} < 1 + \frac{m}{2} \le 2^{\lfloor \log_2 m \rfloor} + 1.$$
Thus the Target Claim holds whenever $3 \mid m$. $\square$

---

## 4. The Conic Box Lemma and Pigeonhole Hensel Lifting

For any odd prime $p \ge 5$, write $m = p^e d$ with $e \ge 1$ and $p \nmid d$. If we choose $x = u d$ and $y = v d$ with $1 \le u < v \le \frac{p^e - 1}{2}$, then:
1. $1 \le x < y \le \frac{p^e - 1}{2} d < \frac{m}{2} < 2^{\lfloor \log_2 m \rfloor} + 1$.
2. $d \mid (y - x)$, hence $d \mid (f(y) - f(x))$.
3. $p^e \mid (f(y) - f(x))$ holds if $p^e \mid \bigl(2(u^2 d^2 + uv d^2 + v^2 d^2) + 1\bigr)$, i.e.,
   $$u^2 + uv + v^2 \equiv c \pmod{p^e}, \qquad \text{where } c \equiv -(2d^2)^{-1} \pmod{p^e}.$$

Note that $\gcd(c, p) = 1$.

### Lemma 2 (Pigeonhole Hensel Lifting)
*Let $p \ge 5$ be a prime, $e_0 \ge 1$, and suppose that for every integer $c$ with $p \nmid c$, there exist integers $u_0, v_0$ satisfying:*
1. $1 \le u_0 < v_0 \le \frac{p^{e_0} - 1}{2}$,
2. $u_0^2 + u_0 v_0 + v_0^2 \equiv c \pmod{p^{e_0}}$,
3. $p \nmid (2u_0 + v_0)$ and $p \nmid (u_0 + 2v_0)$.

*Then the same conclusion holds for every $e \ge e_0$.*

*Proof.* We induct on $e \ge e_0$. The base case $e = e_0$ is the hypothesis. For the inductive step $e - 1 \to e$ ($e > e_0$), let $1 \le u_1 < v_1 \le \frac{p^{e-1} - 1}{2}$ satisfy $u_1^2 + u_1 v_1 + v_1^2 \equiv c \pmod{p^{e-1}}$ with $a := 2u_1 + v_1 \not\equiv 0 \pmod p$ and $b := u_1 + 2v_1 \not\equiv 0 \pmod p$.

Set $u = u_1 + k p^{e-1}$ and $v = v_1 + \ell p^{e-1}$ with $k, \ell \in \{0, 1, \dots, \frac{p-1}{2}\}$. Since $2(e-1) \ge e$,
$$u^2 + uv + v^2 \equiv u_1^2 + u_1 v_1 + v_1^2 + p^{e-1}(a k + b \ell) \pmod{p^e}.$$
Let $w := -\frac{u_1^2 + u_1 v_1 + v_1^2 - c}{p^{e-1}} \in \mathbb{Z}$. As $k$ runs over $\{0, 1, \dots, \frac{p-1}{2}\}$, the residues $a k \pmod p$ form a set $A \subseteq \mathbb{F}_p$ of size $\frac{p+1}{2}$. As $\ell$ runs over $\{0, 1, \dots, \frac{p-1}{2}\}$, the residues $w - b \ell \pmod p$ form a set $B \subseteq \mathbb{F}_p$ of size $\frac{p+1}{2}$. Since $|A| + |B| = p + 1 > p$, by the pigeonhole principle $A \cap B \neq \emptyset$, so there exist $k, \ell \in \{0, 1, \dots, \frac{p-1}{2}\}$ with $ak + b\ell \equiv w \pmod p$.

Then:
- $u^2 + uv + v^2 \equiv c \pmod{p^e}$.
- $1 \le u \le \frac{p^{e-1} - 1}{2} + \frac{p-1}{2} p^{e-1} = \frac{p^e - 1}{2}$, and similarly $1 \le v \le \frac{p^e - 1}{2}$.
- Since $1 \le u_1 < v_1 < p^{e-1}$, we have $u \equiv u_1 \not\equiv v_1 \equiv v \pmod{p^{e-1}}$, so $u \neq v$.
- $2u + v \equiv 2u_1 + v_1 \not\equiv 0 \pmod p$ and $u + 2v \equiv u_1 + 2v_1 \not\equiv 0 \pmod p$.

Swapping $u$ and $v$ if $u > v$ completes the induction. $\square$

### Lemma 3 (Conic Box Lemma for $p \ge 17$)
*For every prime $p \ge 17$ and every $c \in \mathbb{F}_p^\times$, there exist integers $1 \le u < v \le \frac{p-1}{2}$ such that $u^2 + uv + v^2 \equiv c \pmod p$ and $p \nmid (2u + v)(u + 2v)$.*

*Proof (purely algebraic — no Weil bound and no finite prime check required).*

1. *Existence of one point on $X^2 + 3Y^2 \equiv 4c \pmod p$:* As $X$ and $Y$ each range over $\{0, 1, \dots, \frac{p-1}{2}\}$, the sets $\{X^2 \bmod p\}$ and $\{(4c - 3Y^2) \bmod p\}$ each have size $\frac{p+1}{2}$. Since $\frac{p+1}{2} + \frac{p+1}{2} = p + 1 > p$, by the pigeonhole principle there exists $(X_0, Y_0) \in \mathbb{F}_p^2$ with $X_0^2 + 3Y_0^2 \equiv 4c \pmod p$.

2. *Stereographic parametrization:* For every $t \in \mathbb{F}_p$ with $t^2 + 3 \not\equiv 0 \pmod p$, define
   $$X(t) = \frac{X_0(t^2 - 3) - 6 Y_0 t}{t^2 + 3}, \qquad Y(t) = \frac{Y_0(3 - t^2) - 2 X_0 t}{t^2 + 3} \pmod p.$$
   Directly expanding gives $X(t)^2 + 3Y(t)^2 \equiv X_0^2 + 3Y_0^2 \equiv 4c \pmod p$. Moreover, $t \mapsto (X(t), Y(t))$ is injective because
   $$A(t) := X_0(X(t) - X_0) - 3Y_0(Y(t) + Y_0) \equiv \frac{-24c}{t^2 + 3} \not\equiv 0 \pmod p,$$
   $$B(t) := Y_0(X(t) - X_0) + X_0(Y(t) + Y_0) \equiv \frac{-8ct}{t^2 + 3} \pmod p,$$
   so $3 B(t) \equiv t A(t) \pmod p$ uniquely recovers $t$ from $(X(t), Y(t))$.

3. *Avoiding degenerate points:* Among all $t \in \mathbb{F}_p$, exclude:
   - $t^2 + 3 \equiv 0 \pmod p$ (at most $2$ values of $t$);
   - $X(t) \equiv 0 \pmod p$ (forces $3Y(t)^2 \equiv 4c$, at most $2$ values of $t$ by injectivity);
   - $Y(t) \equiv 0 \pmod p$ (forces $X(t)^2 \equiv 4c$, at most $2$ values of $t$);
   - $X(t) \equiv \pm Y(t) \pmod p$ (forces $X(t)^2 \equiv Y(t)^2 \equiv c$, at most $4$ values of $t$);
   - $3Y(t)^2 \equiv c \pmod p$ (forces $X(t)^2 \equiv 3c$ and $Y(t)^2 \equiv 3^{-1}c$, at most $4$ values of $t$).

   In total at most $2 + 2 + 2 + 4 + 4 = 14 < 17 \le p$ values of $t$ are excluded, so there exists $t \in \mathbb{F}_p$ avoiding all five conditions. Folding $X := \min(X(t), p - X(t))$ and $Y := \min(Y(t), p - Y(t))$ yields integers $1 \le X, Y \le \frac{p-1}{2}$ with $X \neq Y$, $X^2 + 3Y^2 \equiv 4c \pmod p$, and $3Y^2 \not\equiv c \pmod p$.

4. *Parity construction of $(u, v)$:*
   - If $X \equiv Y \pmod 2$ and $Y > X$: set $u = \frac{Y - X}{2}$, $v = \frac{X + Y}{2}$. Then $1 \le u < v \le \frac{p-1}{2}$, $4(u^2 + uv + v^2) = X^2 + 3Y^2 \equiv 4c \pmod p$, and $0 < 2u + v, u + 2v < p$.
   - If $X \equiv Y \pmod 2$ and $X > Y$: set $u = \frac{X - Y}{2}$, $v = Y$ (swapping if $u > v$). Then $u \neq v$ (since $u = v \implies X = 3Y \implies 3Y^2 \equiv c \pmod p$), $4(u^2 + uv + v^2) = X^2 + 3Y^2 \equiv 4c \pmod p$, and $0 < 2u + v, u + 2v < p$.
   - If $X \not\equiv Y \pmod 2$: set $u = \frac{p - X - Y}{2}$, $v = Y$ (swapping if $u > v$). Since $p$ is odd, $u \in \mathbb{Z}$, $1 \le u, v \le \frac{p-1}{2}$, $4(u^2 + uv + v^2) = (p - X)^2 + 3Y^2 \equiv 4c \pmod p$, and $u \neq v$ and $p \nmid (2u + v)(u + 2v)$ (as $u = v \implies X + 3Y = p \implies 3Y^2 \equiv c \pmod p$, and $u + 2v = p \implies 3Y - X = p \implies 3Y^2 \equiv c \pmod p$).

In all cases we obtain the desired $(u, v)$. $\square$

---

## 5. Completing the proof for all non-powers of $2$

Let $m$ be any positive integer that is not a power of $2$.

- **Case 1 ($3 \mid m$):** Proved in Section 3.
- **Case 2 (some prime $p \ge 17$ divides $m$):** Write $m = p^e d$ with $p \nmid d$, $e \ge 1$. By Lemmas 3 and 2, there exist $1 \le u < v \le \frac{p^e - 1}{2}$ with $u^2 + uv + v^2 \equiv -(2d^2)^{-1} \pmod{p^e}$. Setting $x = ud$, $y = vd$ gives $1 \le x < y < \frac{m}{2} < 2^{\lfloor \log_2 m \rfloor} + 1$ and $m \mid (f(y) - f(x))$.
- **Case 3 (any of $5^3, 7^3, 11^2, 13^2$ divides $m$):** Direct computation (`verify_conj2.c`, Check 2) confirms the hypothesis of Lemma 2 holds at $e_0 = 3$ for $p \in \{5, 7\}$ and at $e_0 = 2$ for $p \in \{11, 13\}$. By Lemma 2, it holds for all $e \ge e_0$, and setting $x = ud$, $y = vd$ finishes this case exactly as in Case 2.
- **Case 4 (remaining moduli):** Every remaining $m$ has the form
  $$m = 2^a \cdot s, \qquad s \mid 5^2 \cdot 7^2 \cdot 11 \cdot 13, \quad s > 1.$$
  - **Subcase 4a ($a \ge 7$, so $2^a \ge 128$):** Pick any prime $p \in \{5, 7, 11, 13\}$ dividing $s$, and write $m = p^e d$ with $p \nmid d$ (so $e \in \{1, 2\}$ for $p \in \{5, 7\}$, $e = 1$ for $p \in \{11, 13\}$, and $d \ge 2^a \ge 128 > 2 p^e - 2$ since $p^e \le 49$).
    We seek $y = x + t d$ with $1 \le t \le \frac{p^e - 1}{2}$, $1 \le x \le p^e$, and $p^e \mid \bigl(2(x^2 + xy + y^2) + 1\bigr)$.
    Completing the square (valid since $\gcd(6, p) = 1$), $2(x^2 + x(x+td) + (x+td)^2) + 1 \equiv 0 \pmod{p^e}$ is equivalent to
    $$(6x + 3td)^2 \equiv -3(td)^2 - 6 \pmod{p^e}.$$
    For each $p \in \{5, 7, 11, 13\}$, we check directly that there exists $t_0 \in \{1, \dots, (p-1)/2\}$ such that $-3(t_0 d)^2 - 6$ is a **nonzero** quadratic residue modulo $p$ (independently of $d \not\equiv 0 \pmod p$, since $\{ (t d)^2 \bmod p : 1 \le t \le (p-1)/2 \} = (\mathbb{F}_p^\times)^2$):
    - $p = 5$: taking $u = (t_0 d)^2 \equiv 1 \pmod 5$ gives $-3(1) - 6 = -9 \equiv 1 = 1^2 \pmod 5$.
    - $p = 7$: taking $u \equiv 2 \pmod 7$ gives $-3(2) - 6 = -12 \equiv 2 = 3^2 \pmod 7$.
    - $p = 11$: taking $u \equiv 1 \pmod{11}$ gives $-3(1) - 6 = -9 \equiv 2$ (non-QR); taking $u \equiv 3 \pmod{11}$ gives $-3(3) - 6 = -15 \equiv 7$ (non-QR); taking $u \equiv 4 \pmod{11}$ gives $-3(4) - 6 = -18 \equiv 4 = 2^2 \pmod{11}$.
    - $p = 13$: taking $u \equiv 1 \pmod{13}$ gives $-3(1) - 6 = -9 \equiv 4 = 2^2 \pmod{13}$.

    Thus in all four cases there is a $t \in \{1, \dots, \frac{p-1}{2}\} \subseteq \{1, \dots, \frac{p^e-1}{2}\}$ such that $-3(td)^2 - 6 \equiv s_0^2 \not\equiv 0 \pmod p$. By Hensel's lemma, there exists $s \in \mathbb{Z}$ with $s^2 \equiv -3(td)^2 - 6 \pmod{p^e}$, and since $\gcd(6, p^e) = 1$ there is a unique $x \in \{1, \dots, p^e\}$ with $6x + 3td \equiv s \pmod{p^e}$. Setting $y = x + td$ gives $m \mid (f(y) - f(x))$ and
    $$1 \le x < y = x + td \le p^e + \frac{p^e - 1}{2} d \le \frac{p^e d}{2} + 1 = \frac{m}{2} + 1 \le 2^{\lfloor \log_2 m \rfloor} + 1,$$
    since $d \ge 2p^e - 2$.
  - **Subcase 4b ($0 \le a \le 6$):** There are exactly $7 \times (3 \cdot 3 \cdot 2 \cdot 2 - 1) = 245$ such moduli $m$. All $245$ are verified directly by `verify_conj2.c` (Check 3) to have a collision $1 \le x < y \le 2^{\lfloor \log_2 m \rfloor} + 1$.

This exhausts all positive integers $m$ that are not powers of $2$, completing the proof of Conjecture 2. $\blacksquare$
