按约定先讲三件事：

1. 这个 lemma 是什么

设 DQM 给了 $|t^{-1}(\sqrt{p_{θ+tu}} - \sqrt{p_θ}) - \tfrac12\langle u, ℓ\rangle\sqrt{p_θ}|{L^2} \to 0$（沿 $t\to 0$）。要证：
$$\int (\sqrt{p{θ+tu}} - \sqrt{p_θ})^2, dμ \to 0 \quad (\text{即 }\sqrt{p_{θ+tu}} \to \sqrt{p_θ}\text{ in }L^2).$$

2. 数学上为什么成立

由三角不等式（L² 范数）：
$$|\sqrt{p_{θ+tu}} - \sqrt{p_θ}|{L^2} \leq |t| \cdot |t^{-1}(\sqrt{p{θ+tu}} - \sqrt{p_θ}) - \tfrac12\langle u,ℓ\rangle\sqrt{p_θ}|{L^2} + |t| \cdot |\tfrac12\langle u,ℓ\rangle\sqrt{p_θ}|{L^2}.$$

第一项 = $|t| \cdot o(1) \to 0$，第二项 = $|t| \cdot (\text{常数}) \to 0$。合起来平方后积分也 → 0。

写 L4 之前，我发现个架构选择，问你一下再动手。

L4 (SqrtSumConvergence) 的证明骨架是：

由 RescaledL2Convergence 可得 $(\sqrt{p_{θ+tu}} - \sqrt{p_θ}) = t \cdot f_t + (t/2)\langle u, \ell\rangle\sqrt{p_θ}$，其中 $f_t$ 是残差项
平方后积分：$\int (\sqrt{p_{θ+tu}} - \sqrt{p_θ})^2, dμ \leq 2t^2 \int f_t^2 + (t^2/2) \int \langle u, \ell\rangle^2 p_θ, dμ$
两项都 $\to 0$（因 $t^2 \to 0$），夹逼得证
这段需要 3 个工程细节：逐点不等式 (a+b)² ≤ 2(a²+b²)、积分单调性、Filter.Tendsto.squeeze。实际估计 40-60 分钟 Lean 工作量，不算轻。

我有个架构简化方案：把 L4 删了，把 SqrtSumConvergence 作为独立假设放进 score_mean_zero。这样两个 L² 收敛事实都是从 DQM 来的，L3 一个 sorry（难的核心），L4 压根不用存在——用户（也就是未来证 Gaussian 实例的人）只需同时证两个 L² 事实即可。

1. 这个 lemma 是什么

如果 $f_t \to f$ 和 $g_t \to g$ 都在 L²(μ) 意义下（即 $\int (f_t-f)^2 \to 0$ 和 $\int (g_t-g)^2 \to 0$），那么：
$$\int f_t g_t, dμ \to \int f g, dμ.$$

2. 数学上为什么成立

关键恒等式：$f_t g_t - f g = (f_t - f) g_t + f (g_t - g)$。两边积分后用 Cauchy-Schwarz：
$$\left|\int (f_t-f) g_t, dμ\right| \leq |f_t - f|{L^2} \cdot |g_t|{L^2}$$
$$\left|\int f (g_t-g), dμ\right| \leq |f|{L^2} \cdot |g_t - g|{L^2}$$

7.2 Theorem. Suppose that $\Theta$ is an open subset of $\mathbb{R}^k$ and that the model $(P_\theta : \theta \in \Theta)$ is differentiable in quadratic mean at $\theta$. Then

[断言 A]  $\quad P_\theta \ell_\theta = 0$

and the Fisher information matrix

[断言 B]  $\quad I_\theta = P_\theta \ell_\theta \ell_\theta^\top \text{ exists}$

Furthermore, for every converging sequence $h_n \to h$, as $n \to \infty$,

[断言 C 即方程 (7.2)]
$$\log \prod_{i=1}^n \frac{p_{\theta + h_n/\sqrt{n}}}{p_\theta}(X_i) = \frac{1}{\sqrt{n}} \sum_{i=1}^n h^\top \ell_\theta(X_i) - \frac{1}{2} h^\top I_\theta h + o_{P_\theta}(1)$$
