# Undecidability of global controllability for continuous-time bilinear systems

## 0. Main result and conventions

We study the homogeneous continuous-time bilinear plant

(0.1)

```math
\dot x(t)=\left(A+\sum_{i=1}^{m}u_i(t)B_i\right)x(t),
\qquad x(t)\in\mathbb R^n.
```

The input is unconstrained: $`u_i(t)\in\mathbb R`$. The main theorem initially takes $`u`$ to be piecewise constant with finitely many pieces on every finite time interval.

The origin is an equilibrium for every input. Following the standard convention for homogeneous bilinear systems, global controllability is therefore defined on the punctured state space

```math
\mathbb R^n_*:=\mathbb R^n\setminus\{0\}.
```

The system is globally controllable if

(0.2)

```math
\forall x,y\in\mathbb R^n_* \ \exists T\geq0\ \exists u:
\quad x(T;x,u)=y.
```

This is the state-to-state controllability definition used in the control literature; see Elliott, *Bilinear Control Systems: Matrices in Action*, Definitions 1.9--1.10 and §1.6.3. In particular, Elliott explicitly notes that the origin is invariant and uses $`\mathbb R^n_*`$ as the state region for homogeneous bilinear systems.

### Main theorem

**Theorem A (main rational-data theorem).** There is no algorithm deciding global controllability for continuous-time homogeneous bilinear systems (0.1) with rational matrices $`A,B_i\in\mathbb Q^{n\times n}`$, with $`n`$ and the number of controls $`m`$ part of the input.

**Theorem A+ (stronger integer-data theorem).** The same undecidability holds when all matrices have integer entries. More strongly, the reduction can ensure

(0.3)

```math
A=\mathrm{diag}(1,0,\ldots,0),
```

and pairwise commuting control matrices $`B_1,\ldots,B_m`$, with $`n\ge 2`$. Undecidability here means that a partial computable algorithm cannot halt and answer correctly on every input satisfying this promise.

We prove Theorem A+ by an effective many-one reduction from Hilbert's tenth problem. Theorem A follows because every integer instance is also a rational instance.

The proof is for piecewise-constant controls. Section 6 separately proves that, on the constructed instances, the answer is unchanged for every control class $`\mathcal U`$ satisfying

(0.4)

```math
\mathcal U_{\rm pc}\subseteq\mathcal U\subseteq L^1_{\rm loc}.
```

In particular this includes piecewise-continuous controls and all locally integrable controls. The $`L^1_{\rm loc}`$ extension is not used in the main proof.

The reduction encodes integer solvability as a sign condition (Lemma 2.1)
and realizes that condition as a coefficient of a commuting rational matrix
family (Section 3). The feedback construction then turns the sign condition
into a controllability test (Theorem 4.1). A rational change of coordinates
and denominator clearing put the resulting plant in the form required by
Theorem A+ (Section 5).

------------------------------------------------------------------------

## 1. Piecewise-constant controls as a matrix semigroup

For $`u=(u_1,\ldots,u_m)\in\mathbb R^m`$, put

```math
M(u):=A+\sum_{i=1}^m u_iB_i.
```

A piecewise-constant input with successive constant values $`u^{(1)},\ldots,u^{(k)}`$ on intervals of lengths $`t_1,\ldots,t_k\gt 0`$ has transition matrix

(1.1)

```math
P=e^{t_kM(u^{(k)})}\cdots e^{t_1M(u^{(1)})}.
```

Conversely every such finite product is realized by a piecewise-constant input. The empty product is the identity and corresponds to time zero.

Define the transition semigroup

(1.2)

```math
\mathcal S(A;B_1,\ldots,B_m)
:=
\left\{
I,\ 
e^{t_kM(u^{(k)})}\cdots e^{t_1M(u^{(1)})}
\right\},
```

where $`k\geq1`$, $`t_j\gt 0`$, and $`u^{(j)}\in\mathbb R^m`$ are arbitrary.

Every matrix exponential is invertible and

```math
\det(e^{tM})=e^{t\,\mathrm{tr}M}\gt 0.
```

Hence $`\mathcal S\subseteq GL^+(n,\mathbb R)`$, where $`GL^+`$ denotes the matrices of positive determinant.

**Definition 1.1 (piecewise-constant global controllability).** The plant is globally controllable on $`\mathbb R^n_*`$ if and only if

(1.3)

```math
\forall x,y\ne0\quad \exists P\in\mathcal S:\ Px=y.
```

This is exactly (0.2) for piecewise-constant controls.

The proof will construct systems for which

(1.4)

```math
\mathcal S=
\begin{cases}
GL^+(n,\mathbb R),&\text{if the source Diophantine equation has a solution},\\ \text{a semigroup preserving a proper cone},&\text{otherwise}.
\end{cases}
```

## 2. A rational sign encoding of Hilbert's tenth problem

Let

```math
p(k_1,\ldots,k_s)=\sum_{\alpha}p_\alpha k^\alpha
\in\mathbb Z[k_1,\ldots,k_s]
```

be an instance of Hilbert's tenth problem. Set $`d=\max(1,\deg p)`$, using degree zero for the zero polynomial, and homogenize:

(2.1)

```math
Q(q_0,\ldots,q_s)
=
\sum_{\alpha}p_\alpha q_0^{d-|\alpha|}
q_1^{\alpha_1}\cdots q_s^{\alpha_s}.
```

Thus $`Q`$ is homogeneous of degree $`d`$, and

(2.2)

```math
Q(\pi,\pi k_1,\ldots,\pi k_s)=\pi^d p(k_1,\ldots,k_s).
```

Let $`H=\sum_\alpha|p_\alpha|`$, the coefficient $`\ell^1`$-norm of $`Q`$, and set

```math
\kappa:=2^{d+1}d(H+1),\qquad
R(q):=1+\sum_{i=0}^s q_i^2,
```

```math
g(q_0,a):=(q_0-3)(4-q_0)-a^2.
```

For variables $`q_0,\ldots,q_s,a`$ and $`s_0,\ldots,s_s`$, define

(2.3)

```math
F(q,s,a):=
Q(q)^2+
\kappa^2R(q)^{d-1}
\left(\sum_{i=0}^s s_i^2+g(q_0,a)^2\right)-1.
```

This is a polynomial with integer coefficients. At the rational/integer base point

```math
q_i=0,\quad s_i=0,\quad a=0,
```

we have $`Q(0)=0`$, $`R(0)=1`$, and $`g(0,0)=-12`$. Therefore

(2.4)

```math
F(0,0,0)=144\kappa^2-1\gt 0.
```

### Lemma 2.1 (sign encoding)

```math
\exists(q_0,\ldots,q_s,a)\in\mathbb R^{s+2}:
F(q,s,a)\lt 0
```

along the oscillator constraints $`s_i=\sin q_i`$ if and only if

(2.5)

```math
\exists k\in\mathbb Z^s:\ p(k)=0.
```

**Proof.**

*Forward construction from an integer zero.* If $`p(k)=0`$, take

```math
q_0=\pi,\qquad q_i=\pi k_i,\qquad
a=\sqrt{(\pi-3)(4-\pi)}.
```

Then $`s_i=\sin q_i=0`$, $`g(q_0,a)=0`$, and (2.2) gives $`Q(q)=0`$. Thus $`F=-1\lt 0`$.

*Rounding in the converse direction.* Suppose $`F\lt 0`$ on the oscillator constraints. Since every term in (2.3) before the final $`-1`$ is nonnegative,

(2.6)

```math
|Q(q)|\lt 1,\qquad
|\sin q_i|\lt 
\frac{1}{\kappa R(q)^{(d-1)/2}},\qquad
|g(q_0,a)|\lt \frac1\kappa\le\frac14.
```

If $`q_0\notin(2,5)`$, then $`(q_0-3)(4-q_0)\le-2`$, and subtracting $`a^2`$ cannot increase it. This contradicts the last inequality in (2.6). Hence $`q_0\in(2,5)`$.

For each $`i`$, choose a nearest integer $`n_i`$ to $`q_i/\pi`$, and put $`q_i^*=\pi n_i`$. If $`\delta_i=|q_i-q_i^*|\le\pi/2`$, then

```math
|\sin q_i|=\sin\delta_i\ge \frac{2}{\pi}\delta_i.
```

Consequently

(2.7)

```math
|q_i-q_i^*|
\le\frac{\pi}{2}|\sin q_i|
\lt 
\frac{2}{\kappa R(q)^{(d-1)/2}}
\le\frac12.
```

Since $`q_0\in(2,5)`$, the only multiple of $`\pi`$ within distance $`1/2`$ is $`\pi`$; thus $`n_0=1`$.

Along the segment joining $`q`$ to $`q^*`$, every coordinate has absolute value at most $`2\sqrt{R(q)}`$. Homogeneity and the coefficient bound give

```math
\sum_{i=0}^s|\partial_iQ(\xi)|
\le dH\bigl(2\sqrt{R(q)}\bigr)^{d-1}.
```

The mean-value estimate and (2.7) now imply

```math
\begin{aligned}
|Q(q^*)-Q(q)|
&\le
\frac{2}{\kappa R(q)^{(d-1)/2}}\,
dH\bigl(2\sqrt{R(q)}\bigr)^{d-1}\\ &=\frac{2^d dH}{\kappa}
=\frac{H}{2(H+1)}\lt \frac12.
\end{aligned}
```

Together with $`|Q(q)|\lt 1`$, this yields $`|Q(q^*)|\lt 3/2`$. But

```math
Q(q^*)=\pi^d p(n_1,\ldots,n_s).
```

If the integer $`p(n)`$ were nonzero, its absolute value would be at least one, so $`|Q(q^*)|\ge\pi^d\gt 3`$, a contradiction. Hence $`p(n)=0`$. $`\square`$

The appearance of $`\pi`$ is only in the analysis of possible witnesses. All input coefficients in (2.3) are integers.

## 3. A finite-dimensional rational representation

We next turn the scalar function in Lemma 2.1 into a matrix coefficient of a commuting rational matrix family.

Let the base variables be

```math
z=(q_0,\ldots,q_s,c_0,\ldots,c_s,s_0,\ldots,s_s,a).
```

For $`i=0,\ldots,s`$, define the affine-linear vector field

(3.1)

```math
V_i=\partial_{q_i}-s_i\partial_{c_i}+c_i\partial_{s_i},
\qquad
V_a=\partial_a.
```

These vector fields commute pairwise. Their flows from the base point

```math
z_*:\quad q_i=0,\ c_i=1,\ s_i=0,\ a=0
```

satisfy

(3.2)

```math
q_i(t)=t_i,\qquad c_i(t)=\cos t_i,\qquad s_i(t)=\sin t_i,
\qquad a(t)=t_a.
```

Let $`D_0=2d+2`$, the total-degree bound for $`F`$. Let $`\mathcal P_{\le D_0}`$ be the finite-dimensional rational vector space of polynomials of total degree at most $`D_0`$ in the coordinates $`z`$. Each derivation $`V_i,V_a`$ preserves this space: differentiation lowers degree by one, and multiplication by a coordinate raises it by at most one. In the monomial basis, the induced matrices have integer entries. The induced matrices commute because the vector fields commute.

Let $`\Psi(z)`$ be the column of all monomials of degree at most $`D_0`$. There are integer matrices $`K_0,\ldots,K_s,K_a`$ such that along a constant combination of the vector fields,

```math
\frac{d}{dt}\Psi(z(t))
=
\left(\sum_{i=0}^s u_iK_i+u_aK_a\right)\Psi(z(t)).
```

Put $`b_0=\Psi(z_*)`$, and let $`\ell_0`$ be the coefficient row of $`F/F(z_*)`$. Then

(3.3)

```math
\ell_0
\exp\left(\sum_{i=0}^s t_iK_i+t_aK_a\right)b_0
=
\frac{F(q,\sin q,a)}{F(z_*)}.
```

All data are rational, and $`\ell_0b_0=1`$.

### Reachable/observable reduction

The full monomial representation need not be cyclic or observable. Enforce both properties as follows. Let

```math
W:=\mathrm{span}_{\mathbb Q}
\{K_{i_1}\cdots K_{i_k}b_0:k\ge0\}
```

be the reachable subspace. It is invariant under every $`K_i`$. Define

```math
N:=\{w\in W:
\ell_0K_{i_1}\cdots K_{i_k}w=0
\text{ for every finite word }(i_1,\ldots,i_k)\}.
```

Then $`N`$ is invariant under all $`K_i`$. Pass to the quotient $`V=W/N`$, with induced matrices $`K_i`$, vector $`b`$, and row $`\ell`$. This construction is effective over $`\mathbb Q`$. Let $`D`$ be the dimension of the original representation. Reachable word states of length at most $`D`$ span $`W`$, since the spans stabilize once two successive spans agree. The corresponding argument on the dual shows that output tests on words of length at most $`D`$ already determine $`N`$. Form the table

```math
H_{u,v}=\ell_0 K_u K_v b_0
```

over these bounded words $`u,v`$, where $`K_u`$ denotes the ordered product of the matrices indexed by $`u`$. A column is the list of observations of the reachable state $`K_vb_0`$. Rational Gaussian elimination selects columns whose classes form a basis of $`W/N`$, and the pivot rows give an invertible observation matrix on that basis. Solving with this matrix gives the coordinates of $`b`$ and of the induced operators $`K_i`$. Evaluating the original output on the basis gives $`\ell`$.

**Lemma 3.1 (cyclicity and observability of the quotient).** The column span of the exponential orbit equals the span of all word vectors $`K_{i_1}\cdots K_{i_k}b_0`$: the exponential orbit lies in the word-generated invariant subspace by its convergent series, and its span is finite-dimensional and therefore closed; the span of the orbit is invariant under each $`e^{tK_i}`$, because multiplication by $`e^{tK_i}`$ sends orbit vectors to orbit vectors. Differentiating $`e^{tK_i}z`$ at zero for every $`z`$ in that span gives invariance under each $`K_i`$. The dual argument applies to the row orbit. After quotienting by $`N`$, the common row annihilator is zero, so the row orbit spans the full dual.

The resulting representation satisfies

(3.4)

```math
\ell b=1,
```

(3.5)

```math
\mathrm{span}_{\mathbb R}
\left\{\exp\left(\sum_i t_iK_i\right)b:t\in\mathbb R^{s+2}\right\}=V_{\mathbb R},
```

(3.6)

```math
\mathrm{span}_{\mathbb R}
\left\{\ell\exp\left(\sum_i t_iK_i\right):t\in\mathbb R^{s+2}\right\}
=V_{\mathbb R}^*.
```

Here $`V_{\mathbb R}=V\otimes_{\mathbb Q}\mathbb R`$, identified with a real coordinate space after choosing a rational basis. The matrices $`K_i`$ still commute.

Let

(3.7)

```math
G:=\left\{\exp\left(\sum_i t_iK_i\right):t_i\in\mathbb R\right\}.
```

Because the $`K_i`$ commute, $`G`$ is a subgroup of $`GL(V_{\mathbb R})`$. The exponential coefficient in (3.3) is preserved by restricting to $`W`$ and passing to $`W/N`$. Lemma 2.1 then gives

(3.8)

```math
\bigl(\exists g\in G:\ell gb\lt 0\bigr)
\iff
\bigl(\exists k\in\mathbb Z^s:p(k)=0\bigr).
```

## 4. The feedback theorem

This section is the main control-theoretic construction.

Let $`V`$ be a finite-dimensional real vector space, $`K_1,\ldots,K_r`$ commuting endomorphisms, $`b\in V`$, and $`\ell\in V^*`$, with

(4.1)

```math
\ell b=1,
\quad
\mathrm{span}\{gb:g\in G\}=V,
\quad
\mathrm{span}\{\ell g:g\in G\}=V^*,
```

where $`G=\{\exp(\sum t_iK_i):t_i\in\mathbb R\}`$.

On $`V\oplus\mathbb R`$, put

(4.2)

```math
A=\frac12
\begin{pmatrix}b\\1\end{pmatrix}
\begin{pmatrix}\ell&1\end{pmatrix}
=
\frac12
\begin{pmatrix}b\ell&b\\\ell&1\end{pmatrix},
```

(4.3)

```math
D=\begin{pmatrix}I_V&0\\0&0\end{pmatrix},
\qquad
\widehat K_i=\begin{pmatrix}K_i&0\\0&0\end{pmatrix}.
```

Consider

(4.4)

```math
\dot X=
\left(A+vD+\sum_i u_i\widehat K_i\right)X,
\qquad (u,v)\in\mathbb R^{r+1}.
```

The drift is a rank-one idempotent:

(4.5)

```math
A^2=A,\qquad \mathrm{rank}A=1.
```

The control matrices commute pairwise.

### Theorem 4.1 (feedback sign/global-controllability equivalence)

The piecewise-constant system (4.4) is globally controllable on $`(V\oplus\mathbb R)\setminus\{0\}`$ if and only if

(4.6)

```math
\exists g\in G:\ell gb\lt 0.
```

In the YES case its transition semigroup is exactly

(4.7)

```math
GL^+(\dim V+1,\mathbb R).
```

#### Lemma 4.2 (an invariant cone in the absence of a negative pairing)

Assume

(4.8)

```math
\ell gb\ge0\qquad\text{for every }g\in G.
```

Let

(4.9)

```math
C_0=\{z\in V:\ell gz\ge0\text{ for every }g\in G\},
\qquad
C=C_0\times\mathbb R_{\ge0}.
```

Each inequality defines a closed half-space, so $`C_0`$ and $`C`$ are closed
convex cones. If $`z\in C_0`$ and $`h\in G`$, then $`\ell g(hz)\ge0`$ for every
$`g\in G`$, since $`gh\in G`$. Thus $`C_0`$ is invariant under $`G`$.
By (4.8) it contains every $`gb`$, including $`b`$. The column-spanning
condition in (4.1) therefore gives $`C_0`$ nonempty interior. If both
$`z`$ and $`-z`$ belong to $`C_0`$, all the pairings $`\ell gz`$ vanish.
The row-spanning condition in (4.1) gives $`z=0`$. It follows that $`C`$ is
pointed and has nonempty interior.

Taking $`g=I_V`$ in (4.9) gives $`\ell z\ge0`$ on $`C_0`$, and
$`(b,1)\in C`$. For $`(z,s)\in C`$,

(4.10)

```math
A(z,s)=\frac{\ell z+s}{2}(b,1)\in C.
```

Since $`A^2=A`$,

```math
e^{tA}=I+(e^t-1)A
```

preserves $`C`$ for $`t\ge0`$.

Every control-only matrix

```math
F=vD+\sum_i u_i\widehat K_i
```

has exponential

```math
e^{tF}
=
\mathrm{diag}\left(
e^{tv}\exp\left(t\sum_i u_iK_i\right),1
\right),
```

which preserves $`C`$, for every real $`t`$. The Trotter product formula therefore gives

```math
e^{t(A+F)}
=
\lim_{N\to\infty}
\left(e^{tA/N}e^{tF/N}\right)^N,
\qquad t\ge0.
```

Each approximating product preserves $`C`$, and $`C`$ is closed. Hence every constant-control transition preserves $`C`$. Every piecewise-constant transition does too. In particular, $`(0,1)\in C`$ cannot be steered to $`(0,-1)\notin C`$, so the system is not globally controllable.

#### YES direction: shear matrices lie in the transition-semigroup closure

Let $`S`$ be the actual transition semigroup of (4.4), and let $`\overline S`$ denote its closure in $`GL^+`$.

#### Lemma 4.3 (fast-control limits)

The drift cannot be switched off. Nevertheless, unrestricted controls yield the following fast-control limit. For arbitrary real $`t_i,s`$, run the constant control $`u_i=t_i/\varepsilon`$, $`v=s/\varepsilon`$ for time $`\varepsilon\gt 0`$. The transition is

(4.11)

```math
\exp\left(\varepsilon A+sD+\sum_i t_i\widehat K_i\right)
\longrightarrow
\mathrm{diag}\left(e^s\exp\left(\sum_i t_iK_i\right),1\right).
```

Thus $`\overline S`$ contains every $`\mathrm{diag}(g,1)`$, $`g\in G`$, and every $`e^{sD}`$, $`s\in\mathbb R`$. It is a closed semigroup.

For $`w\in V`$, $`\eta\in V^*`$, write

(4.12)

```math
U_w=\begin{pmatrix}0&w\\0&0\end{pmatrix},
\qquad
L_\eta=\begin{pmatrix}0&0\\\eta&0\end{pmatrix}.
```

#### Lemma 4.4 (positive shear limits)

Conjugating $`A`$ by $`e^{rD}`$ and using a short positive drift interval gives

(4.13)

```math
e^{rD}e^{2te^{-r}A}e^{-rD}
=
\exp\left(
t\begin{pmatrix}
e^{-r}b\ell&b\\ e^{-2r}\ell&e^{-r}
\end{pmatrix}
\right)
\longrightarrow e^{tU_b}
\quad(r\to+\infty).
```

Similarly,

(4.14)

```math
e^{-rD}e^{2te^{-r}A}e^{rD}
\longrightarrow e^{tL_\ell}.
```

All factors on the left belong to $`\overline S`$; hence the limits do too. Since $`U_w^2=L_\eta^2=0`$, these are the shears $`I+tU_b`$ and $`I+tL_\ell`$, $`t\ge0`$.

Conjugating by $`\mathrm{diag}(g,1)`$ gives

(4.15)

```math
I+tU_{gb},\qquad I+tL_{\ell g^{-1}}
\in\overline S
\quad(g\in G,\ t\ge0).
```

#### Lemma 4.5 (a negative pairing reverses the shears)

Now assume (4.6), and choose $`g_0\in G`$ with

```math
\gamma:=\ell g_0b\lt 0.
```

Put $`a=g_0b`$. For any $`\alpha\gt 0`$, choose $`\beta=-1/(\alpha\gamma)\gt 0`$, and set

```math
T=I+\alpha U_a,\qquad L=I+\beta L_\ell,\qquad P=TLT.
```

The decomposition $`V=\mathbb Ra\oplus\ker\ell`$ is direct. On $`\ker\ell\oplus\{0\}`$, $`T,L,P`$ act as the identity. On the plane spanned by $`(a,0)`$ and $`(0,1)`$, their matrices are

```math
T=\begin{pmatrix}1&\alpha\\0&1\end{pmatrix},
\quad
L=\begin{pmatrix}1&0\\-1/\alpha&1\end{pmatrix},
\quad
P=\begin{pmatrix}0&\alpha\\-1/\alpha&0\end{pmatrix}.
```

Therefore $`P^4=I`$ on the full space. Since $`P=TLT`$,

(4.16)

```math
T^{-1}=LTP^3,\qquad L^{-1}=TP^3T.
```

All factors on the right belong to $`\overline S`$. As $`\alpha`$ ranges over the positive reals, so does $`\beta=-1/(\alpha\gamma)`$. Conjugation by $`\mathrm{diag}(h,1)`$ takes the inverse upper shear along $`g_0b`$ to one along $`hg_0b`$, and the inverse lower shear along $`\ell`$ to one along $`\ell h^{-1}`$. These are all the column and row orbit directions. Together with (4.15), this gives shears with arbitrary real parameters along each orbit direction. Products of upper shears add their column directions, and products of lower shears add their row directions. The two spanning conditions in (4.1) now give

(4.17)

```math
I+U_w\in\overline S\quad(w\in V),
\qquad
I+L_\eta\in\overline S\quad(\eta\in V^*),
```

with arbitrary real shear parameters.

In a basis of $`V`$, (4.17) gives all elementary transvections through the scalar coordinate, indexed here by $`0`$. For distinct indices $`i,j`$ in $`V`$, the group commutator of $`I+aE_{i0}`$ and $`I+E_{0j}`$ is $`I+aE_{ij}`$, where $`E_{ij}`$ is a matrix unit. Their inverses are also available by (4.17). Thus $`\overline S`$ contains all elementary transvections, which generate $`SL(\dim V+1,\mathbb R)`$. The matrices $`e^{sD}`$ have determinant $`e^{s\dim V}`$, so they supply every positive determinant. Therefore

(4.18)

```math
\overline S=GL^+(\dim V+1,\mathbb R).
```

#### Exactness of the transition semigroup

To pass from density to exact reachability, we show that $`S`$ has nonempty interior.

First, the Lie algebra generated by $`A,D,\widehat K_i`$ is all of $`\mathfrak{gl}(\dim V+1,\mathbb R)`$. Indeed,

```math
[D,A]=\tfrac12(U_b-L_\ell),\qquad
[D,[D,A]]=\tfrac12(U_b+L_\ell),
```

so $`U_b,L_\ell`$ belong to the generated Lie algebra. Moreover,

```math
[\widehat K_i,U_w]=U_{K_iw},
\qquad
[\widehat K_i,L_\eta]=-L_{\eta K_i}.
```

Iterating these brackets gives the word-generated column and row spans. By the orbit-span argument of Lemma 3.1 and the spanning conditions in (4.1), this gives every upper and lower shear generator. Finally,

```math
[U_w,L_\eta]=
\begin{pmatrix}w\eta&0\\0&-\eta w\end{pmatrix},
```

and these block-diagonal commutators, together with the upper and lower off-diagonal generators, span $`\mathfrak{sl}(\dim V+1,\mathbb R)`$. Since $`\mathrm{tr}A=1`$, the generated Lie algebra is all of $`\mathfrak{gl}`$.

The available constant-control generators include

```math
M_0=A,\quad M_i=A+\widehat K_i,\quad M_D=A+D.
```

Their generated Lie algebra is therefore full as well.

**Lemma 4.6 (full Lie algebra implies interior of the positive-time semigroup).** For finitely many real matrices $`M_1,\ldots,M_q`$, let $`S_+`$ be the semigroup of finite products of $`e^{tM_j}`$, $`t\gt 0`$, together with the identity. If the Lie algebra generated by the $`M_j`$ is $`\mathfrak{gl}(N,\mathbb R)`$, then $`S_+`$ has nonempty interior in $`GL^+(N,\mathbb R)`$.

*Proof.* For each finite word, consider its endpoint map as a function of its positive durations. Let $`r`$ be the largest differential rank attained by any such map, and choose a word $`g`$ attaining it. Right-translate its differential image to the identity and call the resulting $`r`$-dimensional subspace $`W`$.

Append any fixed $`h\in S_+`$, then append a final factor $`e^{tM_j}`$. Right-translated derivatives in the original word parameters still span $`W`$; the derivative in the final parameter is $`\mathrm{Ad}_{gh}M_j`$. Maximality of $`r`$ forces

```math
\mathrm{Ad}_{gh}M_j\in W,
\quad\text{hence}\quad
\mathrm{Ad}_{h}M_j\in\mathrm{Ad}_{g^{-1}}W.
```

Let $`L`$ be the span of all $`\mathrm{Ad}_hM_j`$, for $`h\in S_+`$ and all $`j`$. Then $`L\subseteq\mathrm{Ad}_{g^{-1}}W`$, so $`\dim L\le r`$. It contains each $`M_j`$, and it is invariant under $`\mathrm{Ad}_{e^{tM_i}}`$ for $`t\gt 0`$. Differentiating at $`t=0^+`$ gives $`[M_i,L]\subseteq L`$. Thus $`L`$ contains the Lie algebra generated by all $`M_i`$, which is $`\mathfrak{gl}(N,\mathbb R)`$. Hence $`r=N^2`$. The endpoint map attaining this rank is a submersion at a positive-duration parameter point, so its image contains an open set. $`\square`$

Apply Lemma 4.6 to $`M_0,M_i,M_D`$. The actual semigroup $`S`$ contains a nonempty open set. It is dense in $`GL^+`$ by (4.18).

**Lemma 4.7 (dense semigroup with interior).** If a subsemigroup $`S`$ of a topological group $`G`$ is dense and contains a nonempty open subset $`O`$, then $`S=G`$.

*Proof.* Given $`g\in G`$, the set $`gO^{-1}`$ is nonempty and open. Density gives $`s\in S\cap gO^{-1}`$. Thus $`s=go^{-1}`$ for some $`o\in O`$, so $`g=so\in S`$. $`\square`$

Therefore $`S=GL^+`$. The normalization $`\ell b=1`$ implies $`\dim V\ge 1`$, so $`N=\dim V+1\ge 2`$. Thus $`GL^+(N,\mathbb R)`$ acts transitively on $`\mathbb R^N_*`$, and the system is globally controllable. This proves the YES direction and Theorem 4.1. $`\square`$

## 5. Completing the reduction

By (3.8) and Theorem 4.1,

(5.1)

```math
p\text{ has an integer zero}
\iff
\text{the system constructed from }p
\text{ is globally controllable}.
```

The construction uses only finite rational linear algebra and is effective. If global controllability of rational continuous-time bilinear plants were decidable, Hilbert's tenth problem would be decidable. This contradiction proves undecidability.

### 5.1 Integer matrices and canonical drift

The feedback drift in (4.2) is a rational rank-one idempotent:

```math
A^2=A,\qquad \mathrm{rank}A=1.
```

Its image is spanned by the rational vector $`(b,1)`$, and its kernel is the rational hyperplane

```math
\{(z,s):\ell z+s=0\}.
```

Since $`\ell b=1`$, the vector $`(b,1)`$ is not in that kernel. Choose a rational basis consisting of $`(b,1)`$ and a rational basis of $`\ker(\ell,1)`$. In this basis,

(5.2)

```math
A=\mathrm{diag}(1,0,\ldots,0).
```

All transformed control matrices remain rational and commute.

For each control matrix separately, multiply by a positive integer clearing its denominators. This does not change the admissible family of constant generators, because its corresponding control is unrestricted over $`\mathbb R`$: replacing $`B_i`$ by $`d_iB_i`$, $`d_i\gt 0`$, is exactly the invertible input reparametrization $`u_i\mapsto d_i u_i`$. The resulting matrices are all integral, while the drift remains (5.2).

This proves Theorem A+.

### 5.2 Rational-input theorem

The rational decision problem contains the integer instances as a subclass. Any algorithm deciding global controllability for all rational matrices would decide it for integer matrices. Therefore the rational-input problem is undecidable as well. This completes the proof of Theorem A.

------------------------------------------------------------------------

## 6. Control classes beyond piecewise constant

The same reduction applies to locally integrable controls.

Let $`L^1_{\rm loc}([0,\infty),\mathbb R^m)`$ be the standard class of measurable controls whose components are integrable on every compact interval. For such a control, the coefficient matrix

```math
M(t)=A+\sum_i u_i(t)B_i
```

is locally integrable, and the linear Carathéodory equation has a unique absolutely continuous solution.

### Lemma 6.1 (continuous dependence in $`L^1`$)

Fix $`T\gt 0`$. If $`M_k,M\in L^1([0,T],\mathbb R^{n\times n})`$ and

```math
\|M_k-M\|_{L^1}\to0,
```

then their fundamental matrices, normalized to the identity at zero, satisfy

```math
\sup_{0\le t\le T}\|X_k(t)-X(t)\|\to0.
```

*Proof.* The integral equations are

```math
X_k(t)=I+\int_0^tM_k(s)X_k(s)\,ds,\qquad
X(t)=I+\int_0^tM(s)X(s)\,ds.
```

Gronwall's inequality gives

```math
\sup_{0\le t\le T}\|X_k(t)\|
\le \exp(\|M_k\|_{L^1}),
```

so the left side is uniformly bounded. Subtract the integral equations:

```math
\|X_k(t)-X(t)\|
\le
\int_0^t\|M_k(s)\|\|X_k(s)-X(s)\|\,ds
+
\int_0^t\|M_k(s)-M(s)\|\|X(s)\|\,ds.
```

A second application of Gronwall proves convergence uniformly on $`[0,T]`$. $`\square`$

### Theorem 6.2 (the reduction is unchanged for $`L^1_{\rm loc}`$)

For every polynomial instance $`p`$, the constructed system is globally controllable with piecewise-constant controls if and only if it is globally controllable with $`L^1_{\rm loc}`$ controls.

*Proof.* In a YES instance, piecewise-constant controls already connect every pair, and they belong to $`L^1_{\rm loc}`$.

When there is no negative pairing, Lemma 4.2 shows that every piecewise-constant transition preserves the closed cone $`C`$ defined in (4.9). Let $`u\in L^1([0,T],\mathbb R^m)`$. Approximate it in $`L^1`$ by controls $`u_k`$ constant on the cells of finite uniform partitions of $`[0,T]`$. Such approximants exist by density of continuous controls in $`L^1`$ on the compact interval and uniform approximation of a continuous control by its samples on a fine partition. The map $`u\mapsto A+\sum_i u_iB_i`$ is affine with bounded linear part, so the associated coefficient matrices converge in $`L^1`$. Lemma 6.1 then gives convergence of the fundamental matrices. For every $`x\in C`$, each approximating endpoint $`X_k(T)x`$ belongs to $`C`$. Closedness of $`C`$ implies $`X(T)x\in C`$. Thus every $`L^1_{\rm loc}`$ trajectory preserves $`C`$, and the state $`(0,1)\in C`$ cannot be steered to $`(0,-1)\notin C`$. $`\square`$

The coordinate change and input rescalings in Section 5.1 also preserve
locally integrable reachability. A fixed invertible state map transports
the integral equation, and multiplying individual controls by nonzero
constants is a bijection on the locally integrable controls.

**Corollary 6.3.** The undecidability theorem holds for every control class $`\mathcal U`$ satisfying

```math
\mathcal U_{\rm pc}\subseteq\mathcal U\subseteq L^1_{\rm loc}.
```

The two inclusions give the corresponding inclusions for state reachability. Hence the same constructed integer plant gives the correct answer for every such class, and the canonical promise in Theorem A+ still applies. This includes piecewise-continuous controls and $`L^1_{\rm loc}`$ controls.

The inclusion argument does not cover globally continuous controls, since that class excludes piecewise-constant controls with jumps.

------------------------------------------------------------------------

## 7. Lean verification

[MainTheorems.lean](../MainTheorems.lean) states Theorems A and A+ directly
for matrices. [ControlClassTheorems.lean](../ControlClassTheorems.lean)
states the equivalence for the two control classes on the feedback family
and the outputs of the reduction. The cone in (4.9) is defined in
[FeedbackConeProof.lean](../ContinuousBilinear/FeedbackConeProof.lean).
The passage to locally integrable controls is formalized in
[IntegrableControlConeApproximation.lean](../ContinuousBilinear/IntegrableControlConeApproximation.lean).
[VerifyUndecidability.lean](../scripts/VerifyUndecidability.lean)
formalizes Corollary 6.3 through the inclusions of the induced
reachability relations and checks the axiom dependencies of the
undecidability results.

The undecidability proofs use the integer-solvability theorem from Cameron
Freer's [Hilbert 10 library](https://github.com/cameronfreer/hilbert10).
The [dependency note](hilbert10-dependency.md) lists the pinned versions
and build instructions.

## References

- D. L. Elliott. *Bilinear Control Systems: Matrices in Action*. Springer,
  2009. [DOI](https://doi.org/10.1007/978-1-4020-9613-6). See Definition 1.6
  and Section 1.5.1 for transition products, and Definitions 1.9–1.10 and
  Section 1.6.3 for controllability and the punctured state space.
- D. Larchey-Wendling and Y. Forster. “Hilbert's Tenth Problem in Coq
  (Extended Version).” *Logical Methods in Computer Science* 18(1), 2022.
  [DOI](https://doi.org/10.46298/lmcs-18(1:35)2022).
- Y. Matiyasevich. *Hilbert's Tenth Problem*. MIT Press, 1993.
  [Foreword by M. Davis](https://logic.pdmi.ras.ru/~yumat/H10Pbook/foreword.htm).
