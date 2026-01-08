可以考虑的总方向是：
数学事实在形式化的过程中如何展现出正确的抽象层级
1. 我学到了什么 (reflecive, methodological)
2. 我是怎么做的：讨论technical的部分
3. 证明了什么，以及，形式化如何反过来矫正我们对数学结构的理解

大的内容点：
1. 数学事实
2. 形式化
3. PR

Abelian Simple Group
==
**From textbook to library integration**
1. 数学事实（preliminaries, bridges，可能放到最后再去写）
-----
2. 如何进行了形式化
 - First observation： This is an exercise from _Dummit&Foote_. This exercise doesn't assume the finiteness in the proof that an abelian simple group is isomorphic to ZMod p with p a prime number. In mathlib the initial formalization targeted the finite-group setting(*attatch the original version*). And the isomorphic theorem was also missing. 
 - Task recognization： The original proof idea was to give a proof of finiteness then using the existing infrastructure under the setting of finiteness. The proof started with the theorem `abelianSimpleG_isoOfZMod_prime`. This main proof could be divided into two part: the first one is an existensial proof of prime number p; the second one is the isomorphism between this group and Zmod p. The prime number proof already exists under the assumption of finiteness, the isomorphism theorem also exists already with the name `zmodAddCyclicAddEquiv`. Then the only task left is really the finiteness proof. 
 - Initial proof method： to do
----
3. PR过程：Key: transations from a proof to a proof which accepted by mathlib
    - 3.1初步根据mathlib的风格，自己进行refactoring:
        - formatting(code, comments, naming)
        - 重现证明思路，理清证明结构，查看是否能够精简（我记得旧的zpow lemma到首次PR commit就是一个很好的例子），增加自动化的使用
        - p.s. 由于经验限制，only to my best
 - 接受view以及重构proof structure：
    - mathlib style more in detail: to do（check my commit history）
    - generalization and design decision(instance vs. theorem)
        - 通过这次具体的interaction, 学习到的抽象判断（to do: 哪些抽象判断？）
 - 再次重构：
    - 对中间lemma 再度进行generalization，优化proof的推导路径(to do)
    - 来自viewer的simp_rw和对库的掌握是怎么kill掉我几十行的proof
 - 最终merge
    - 已经跟initial PR commit相差很多，中间经过多次重构。
    - TODO：作为contributer, 我对这次view的，最后的总结？我学到的东西？我观察到的mathlib文化？

Hall Subgroup
==
**How formalization forces us to discover the right abstraction level**
1. 数学事实（todo：放到最后去写）
2. 形式化过程
    - why the text book method failed in Lean(HN 阶数公式，Counting on Set level)
    - why factorization in |G| works and preferable
    - 阐述证明里面technical的点，应该有若干个点
    - why the quotient group version is actually easier
    - An important lemma: the index version of 2nd isomorphism theorem
3. PR: 待定。