# JSP-000793 / Erdős #953：从八次对数损失继续改进

日期：2026-10-03。基线是公开提交仓库 `erdos953-lower-submission` 的提交
`531af19`，其已形式化结果为

\[
M(R)\ge \frac{e^{-1}\sqrt R}{61440(\log R+3)^8},\qquad R\ge1000^4.
\]

同日后续：薄矩形面积与参数选择已完成 Lean 接合，新增精确系数
`1/(32768√10)` 的全部 `R≥e` 下界及全部 `R>0` 分段公式。默认
`lake build` 通过（3,688 jobs），主文件为 `Erdos953SharpLower.lean`；
审计见 `erdos953-sharp-formalization-audit-2026-10-03.json`。第 6 节保留
此前四模块阶段的验证记录，后面补充当前状态。

旧目录 `erdos953-lower` 中的十二次损失记录不是当前基线。基线已经把纵坐标
系数从 `8k²` 改成了 `8k`，并保留首位差的大小；这些不是本轮新贡献。

本轮的两项改进是：用薄矩形取代圆盘；使用更紧的半径估计并同时选择基数和位数。

## 结论及证据状态

以下纸面证明得到参数族下界

\[
\boxed{M(R)\ge\frac{(k-1)^n}{1024k^3}}
\quad(k\ge3,\ n\ge1,\ 10k^{2n}\le R).
\tag{1}
\]

由此对所有 `R≥2560` 得到一个简单的统一显式界

\[
\boxed{M(R)\ge\frac{\sqrt R}{2^{20}(\log R)^3}},
\tag{2}
\]

以及更强的渐近界

\[
\boxed{M(R)\gg\sqrt R\left(\frac{\log\log R}{\log R}\right)^3}.
\tag{3}
\]

这里 `M(R)` 是开圆盘中不含正整数距离的可测集面积的上确界。符号 `≫` 中的
常数绝对且为正。式 (1)–(3) 的完整可测集与参数选择论证写在下文。
式 (1) 及式 (3) 的上述精确常数版本现已完整形式化；式 (2) 保留为此前
纸面证明的简化陈述。新 Lean 文件的核验状态见文末。

## 1. 保持现有数字中心

对数字串 `α=(α₀,…,αₙ₋₁)∈{0,…,k−2}ⁿ`，使用现有中心

\[
x_\alpha=\sum_{j<n}\alpha_j k^j,
\qquad y_\alpha=8k\sum_{j<n}\alpha_j k^{2j}.
\]

若两串不同，令 `i` 为最高不同位，`dⱼ=αⱼ−βⱼ`，并记

\[
D=|d_i|,\quad X=k^i,\quad
b=\left|\sum_{j\le i}d_jk^j\right|,\quad
a=8k\left|\sum_{j\le i}d_jk^{2j}\right|.
\]

现有 `LeadingDigit.lean` 中的界给出

\[
1\le D\le k-2,\quad X\ge1,\quad DX\le kb,\quad b\le2DX,
\]
\[
4kDX^2\le a\le16kDX^2.
\]

因此 `a,b` 是正整数，且

\[
\boxed{b^2\le a\le16k^3b^2}.
\tag{4}
\]

左式由 `b²≤4D²X²≤4kDX²≤a` 得到。右式需要保留首位差的加权下界：
由 `DX≤kb` 和 `X≤kb` 得 `DX²≤k²b²`，再乘 `16k`。这些不等式已出现在
八次损失证明的内部；本轮把它们暴露成矩形扰动所需的接口。

## 2. 薄矩形及整数距离排除

定义

\[
\varepsilon=\frac1{256k^3},\qquad
Q_\alpha=(x_\alpha-\tfrac18,x_\alpha+\tfrac18)
\times(y_\alpha-\tfrac\varepsilon2,y_\alpha+\tfrac\varepsilon2).
\]

横向全宽为 `1/4`，纵向全高为 `ε`，所以

\[
|Q_\alpha|=\frac1{1024k^3}.
\]

取两个不同中心对应的任意两点。分别把横、纵差的符号调整到中心差为正的方向，
其距离可写成

\[
d=\sqrt{(a+v)^2+(b+u)^2},\qquad |u|<\tfrac14,\quad |v|<\varepsilon.
\]

因为 `b≥1`，有 `3b/4≤b+u≤5b/4`；因为 `a≥1`，有
`0<a−ε≤a+v≤a+ε`。由 (4)，`16aε≤b²`。于是

\[
d^2-(a+\varepsilon)^2
\ge(a-\varepsilon)^2+\frac9{16}b^2-(a+\varepsilon)^2
=\frac9{16}b^2-4a\varepsilon
\ge\frac5{16}b^2>0.
\]

另一方面，`b²≤a` 且 `ε≤1/16`，故

\[
(a+1-\varepsilon)^2-d^2
\ge2a(1-2\varepsilon)+(1-2\varepsilon)-\frac{25}{16}b^2
\ge\frac3{16}a+\frac78>0.
\]

这证明

\[
\boxed{a+\varepsilon<d<a+1-\varepsilon}.
\tag{5}
\]

`a∈ℤ`，所以所有跨矩形距离都不是整数。同一矩形内的距离小于其直径
`√((1/4)²+ε²)<1`，也不可能是正整数。

不同数字串的横坐标是不同整数（由 `b≥1`），横向区间长度仅 `1/4`，所以矩形
两两不交。它们的有限并集是开集，且面积恰好为 `(k−1)ⁿ/(1024k³)`。

这一改进的来源是直接比较平方距离的区间端点。用欧氏距离的全方向 Lipschitz
估计会同时压缩两个方向，继续产生六次基数损失；矩形比较只需要压缩纵向。

## 3. 半径估计中消去额外基数

几何级数直接给出

\[
0\le x_\alpha<k^n,
\quad 0\le y_\alpha\le
8k(k-2)\frac{k^{2n}-1}{k^2-1}<8k^{2n},
\]

因为 `k(k−2)<k²−1`。于是中心范数小于 `xα+yα<9k^{2n}`。
矩形中任意点距中心小于 `1`，而 `k^{2n}≥1`，所以所有矩形严格包含于
半径 `10k^{2n}` 的开圆盘。只要 `10k^{2n}≤R`，就得到了 (1)。

基线的 `16k²k^{2n}` 半径界是正确但宽松的，额外的 `k²` 在这里消失。

## 4. 同时选择位数与基数，不损失一个基数因子

设 `A=R/10≥256`。选 `n≥2` 为满足

\[
(2n)^{2n}\le A
\]

的最大整数，再取 `k=⌊A^{1/(2n)}⌋`。则

\[
k\ge2n\ge4,\qquad k^{2n}\le A<(k+1)^{2n}.
\tag{6}
\]

由 `n` 的最大性，

\[
k\le A^{1/(2n)}< [2(n+1)]^{1+1/n}
\]

利用 `2(n+1)≤3ⁿ`（`n≥2` 时由归纳可证），得到

\[
k<6(n+1)\le9n.
\tag{7}
\]

两次 Bernoulli 不等式给出

\[
(k-1)^n=k^n(1-1/k)^n\ge k^n(1-n/k)\ge\tfrac12k^n,
\]
\[
k^n=(k+1)^n(1-1/(k+1))^n\ge\tfrac12(k+1)^n>\tfrac12\sqrt A.
\]

所以

\[
\boxed{(k-1)^n>\tfrac14\sqrt A}.
\tag{8}
\]

组合 (1)、(7)、(8)，得到对每个 `R≥2560` 的显式参数界

\[
M(R)>\frac{\sqrt R}{4096\sqrt{10}\,k^3}
>\frac{\sqrt R}{4096\sqrt{10}\,(9n)^3}.
\tag{9}
\]

由于 `n≥2`，`(2n)^{2n}≥4^{2n}`，所以
`n≤log(R/10)/(2log4)`。由 `log4>9/8`（将 `log2` 的积分在 `3/2` 分割，
有 `log2>1/3+1/4=7/12`），
有 `k<9n<4logR`。再用 `√10<4`，式 (9) 推出 (2)。

注意：这里没有先固定 `k` 再把 `n` 向下取整；`k` 是在选好 `n` 后确定的，
所以 `kⁿ` 和 `√A` 的比值有绝对常数下界。

## 5. log-log 因子的严格渐近推导

令 `L=log A`。最大性给出

\[
2n\log(2n)\le L<2(n+1)\log(2(n+1)).
\]

随着 `R→∞`，`n→∞`；右端与左端的比值趋于 `1`，所以
`L∼2nlog(2n)`。取对数可得 `log L∼log n`，故

\[
n\sim\frac{L}{2\log L}.
\]

再由 `k≤9n` 和 (9) 得到 (3)。事实上，这个参数选择还满足 `k∼2n`，但
证明 (3) 无需这个更强的常数结论。此论证适用于所有充分大的实数半径，
不只是半径的一个稀疏子序列。

## 6. 有限核验与形式化进度

以下四模块记录是同日较早的验证阶段。

独立诊断脚本：`research/verify_953_anisotropic.py`。

- 所有计算使用整数；不依赖浮点平方根或近似对数。
- 穷举 `(k,n)=(3,8),(4,6),(8,5),(16,3),(64,2)` 的非零数字差向量，
  共 433,488 个，验证 (4) 与最坏角点的两项严格平方比较。
- 验证 103 个半径参数，包括 `10(2n)^{2n}` 的跳变点及紧邻其左侧的整数、
  从 `10⁶` 至 `10¹⁰⁰⁰` 的大参数。
- 这些检查用于发现错误，不替代对任意 `k,n,R` 的上文证明。

新模块：

- `AnisotropicGeometry.lean`：任意实参数的矩形扰动距离区间和整数距离间隙。
- `AnisotropicDigits.lean`：现有数字构造的两项平方比值及正整数坐标差。
- `AnisotropicRadius.lean`：严格的 `y<8k^{2n}` 和中心半径 `<9k^{2n}`。
- `AnisotropicParameters.lean`：在 `2n≤k` 和取根网格条件下的两次 Bernoulli
  不等式及 `(k−1)ⁿ>√A/4`，尚未形式化满足条件的 `n,k` 存在性。

上述四个模块的 11 个新定理分别通过 `lake env lean` 核验，公理审计只列
`propext`、`Classical.choice`、`Quot.sound`，无证明占位符或新增公理。
最终四模块统一 `lake build` 构建成功（3140 jobs），新模块无警告；构建重放了
基线已有的 `push_neg` 废弃提示及一个未使用 simp 参数提示。精确核验摘要保存于
`research/erdos953-anisotropic-verification-2026-10-03.json`。
尚缺可测矩形并集、面积等式、半径包含和
统一参数选择到 `M(R)` 的 Lean 接合。现有默认提交入口尚未导入这些研究模块，
旧八次损失提交的陈述保持其已验证状态。

复现 Lean 核验（在 `erdos953-lower-submission` 目录，Lean v4.32.2 与已固定的
Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`）：

```powershell
lake build Erdos953Lower.AnisotropicGeometry Erdos953Lower.AnisotropicDigits Erdos953Lower.AnisotropicRadius Erdos953Lower.AnisotropicParameters
```

同日后续新增 `AnisotropicRectangles`、`AnisotropicSelection`、
`AnisotropicLogBounds`、`AnisotropicLogCertificates`、`AnisotropicUniform`
和主文件 `Erdos953SharpLower.lean`。已证明可测矩形并集、精确面积、半径
包含、统一参数存在性、十个有限基数估计及全部半径的最终下界。默认入口
`Erdos953Growth.lean` 已导入新主文件；在同一固定版本环境中运行
`lake build` 即包含全部新定理，最终构建成功（3,688 jobs）。

## 7. 来源、局限和下一方向

数字构造和首位估计沿用 Sárközy 路线；参考 Goenka–Moore，
[Point sets avoiding near-integer distances, arXiv:2605.06621v1](https://arxiv.org/html/2605.06621v1)，
特别是第 3 节的构造和平方根间隙引理。`8k` 缩放与加权首位界来自本仓库已经
完成的八次损失改进。薄矩形扰动、紧半径和协调参数选择是本轮在该构造上的
推导；没有声称已完成全面的新颖性审查。

本结果与现有 `O(√R)` 上界之间仍差 `(logR/loglogR)³`。它没有证明
`M(R)≍√R`，也不自动解决官方对“原题完整解”的认定。

本数字族的坏情况确实出现三次基数尺度：最高差为 `1`、所有低位差为 `−(k−2)`，
当位数增长时，`b≈kⁱ/(k−1)` 而 `a≈8k·k^{2i}`，所以 `b²/a≈1/(8k³)`。
若保持全部数字串及每个矩形相同的纵向厚度，要继续去掉这些三次损失，单纯
优化常数不足。后续可检查删去少量端点附近数字串、非均匀厚度或改变中心编码，
但需要同时控制删点造成的计数损失。
