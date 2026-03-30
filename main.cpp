#include <stdio.h>
#include <stdint.h>
#include <time.h>

namespace RsaImport
{
    typedef int8_t      INT8;
    typedef uint8_t     UINT8;
    typedef int16_t     INT16;
    typedef uint16_t    UINT16;
    typedef int32_t     INT32;
    typedef uint32_t    UINT32;
    typedef int64_t     INT64;
    typedef uint64_t    UINT64;

    struct UINT128
    {
        UINT64 hi;
        UINT64 lo;
    };

    struct RSAI_ENCRYPT_DATA
    {
        UINT64 hi;
        UINT64 lo;
    };

    struct RSAI_PUBLIC
    {
        UINT128 n;
        UINT128 e;
    };

    struct RSAI_PRIVATE
    {
        UINT128 n;
        UINT128 d;

        UINT64 p;
        UINT64 q;
        UINT64 dp;
        UINT64 dq;
        UINT64 qinv;
    };

    static UINT128 MakeU128(UINT64 hi, UINT64 lo)
    {
        UINT128 x;
        x.hi = hi;
        x.lo = lo;
        return x;
    }

    static UINT128 MakeU128U64(UINT64 x)
    {
        UINT128 r;
        r.hi = 0;
        r.lo = x;
        return r;
    }

    static int U128IsZero(UINT128 a)
    {
        return (a.hi == 0 && a.lo == 0);
    }

    static int U128Eq(UINT128 a, UINT128 b)
    {
        return a.hi == b.hi && a.lo == b.lo;
    }

    static int U128Lt(UINT128 a, UINT128 b)
    {
        if (a.hi != b.hi) return a.hi < b.hi;
        return a.lo < b.lo;
    }

    static int U128Ge(UINT128 a, UINT128 b)
    {
        return !U128Lt(a, b);
    }

    static UINT128 U128Add(UINT128 a, UINT128 b)
    {
        UINT128 r;
        r.lo = a.lo + b.lo;
        r.hi = a.hi + b.hi + (r.lo < a.lo ? 1ULL : 0ULL);
        return r;
    }

    static UINT128 U128Sub(UINT128 a, UINT128 b)
    {
        UINT128 r;
        r.lo = a.lo - b.lo;
        r.hi = a.hi - b.hi - (a.lo < b.lo ? 1ULL : 0ULL);
        return r;
    }

    static UINT128 U128Shl1(UINT128 a)
    {
        UINT128 r;
        r.hi = (a.hi << 1) | (a.lo >> 63);
        r.lo = (a.lo << 1);
        return r;
    }

    static int U128GetBit(UINT128 a, int bit)
    {
        if (bit < 64) return (int)((a.lo >> bit) & 1ULL);
        return (int)((a.hi >> (bit - 64)) & 1ULL);
    }

    static void PrintU128Hex(UINT128 x)
    {
        printf("0x%016llx%016llx",
            (unsigned long long)x.hi,
            (unsigned long long)x.lo);
    }

    static UINT128 Mul64Wide(UINT64 a, UINT64 b)
    {
        UINT64 a0 = (UINT32)a;
        UINT64 a1 = a >> 32;
        UINT64 b0 = (UINT32)b;
        UINT64 b1 = b >> 32;

        UINT64 p00 = a0 * b0;
        UINT64 p01 = a0 * b1;
        UINT64 p10 = a1 * b0;
        UINT64 p11 = a1 * b1;

        UINT64 mid = (p00 >> 32) + (UINT32)p01 + (UINT32)p10;

        UINT128 r;
        r.hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
        r.lo = (mid << 32) | (UINT32)p00;
        return r;
    }

    static UINT64 GcdU64(UINT64 a, UINT64 b)
    {
        while (b)
        {
            UINT64 t = a % b;
            a = b;
            b = t;
        }
        return a;
    }

    static UINT64 AddModU64(UINT64 a, UINT64 b, UINT64 mod)
    {
        if (a >= mod) a %= mod;
        if (b >= mod) b %= mod;
        if (a >= mod - b) return a - (mod - b);
        return a + b;
    }

    static UINT64 MulModU64(UINT64 a, UINT64 b, UINT64 mod)
    {
        UINT64 r = 0;
        while (b)
        {
            if (b & 1ULL) r = AddModU64(r, a, mod);
            b >>= 1;
            if (b) a = AddModU64(a, a, mod);
        }
        return r;
    }

    static UINT64 PowModU64(UINT64 a, UINT64 e, UINT64 mod)
    {
        UINT64 r = 1 % mod;
        while (e)
        {
            if (e & 1ULL) r = MulModU64(r, a, mod);
            e >>= 1;
            if (e) a = MulModU64(a, a, mod);
        }
        return r;
    }

    static int IsPrimeU64(UINT64 n)
    {
        static const UINT64 testPrimes[] = {
            2ULL, 3ULL, 5ULL, 7ULL, 11ULL, 13ULL, 17ULL, 19ULL, 23ULL, 29ULL, 31ULL, 37ULL
        };
        static const UINT64 bases[] = {
            2ULL, 325ULL, 9375ULL, 28178ULL, 450775ULL, 9780504ULL, 1795265022ULL
        };

        UINT64 d;
        int s, i, j;

        if (n < 2) return 0;

        for (i = 0; i < (int)(sizeof(testPrimes) / sizeof(testPrimes[0])); ++i)
        {
            UINT64 p = testPrimes[i];
            if (n == p) return 1;
            if ((n % p) == 0) return 0;
        }

        d = n - 1;
        s = 0;
        while ((d & 1ULL) == 0)
        {
            d >>= 1;
            ++s;
        }

        for (i = 0; i < (int)(sizeof(bases) / sizeof(bases[0])); ++i)
        {
            UINT64 a = bases[i] % n;
            UINT64 x;

            if (a == 0) continue;

            x = PowModU64(a, d, n);
            if (x == 1 || x == n - 1) continue;

            for (j = 1; j < s; ++j)
            {
                x = MulModU64(x, x, n);
                if (x == n - 1) break;
            }
            if (j == s) return 0;
        }

        return 1;
    }

    static UINT64 g_rng_state = 0x9e3779b97f4a7c15ULL;

    static UINT64 RandomU64(void)
    {
        UINT64 z = (g_rng_state += 0x9e3779b97f4a7c15ULL);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        z = z ^ (z >> 31);
        return z;
    }

    static void SeedU64(UINT64 seed)
    {
        if (seed == 0)
            seed = (UINT64)time(NULL) ^ 0x123456789abcdef1ULL;

        g_rng_state = seed;
        RandomU64();
        RandomU64();
        RandomU64();
    }

    static UINT64 GeneratePrime63Bit(void)
    {
        for (;;)
        {
            UINT64 x = RandomU64();
            x &= 0x7fffffffffffffffULL;
            x |= 0x4000000000000000ULL;
            x |= 1ULL;

            if (!IsPrimeU64(x)) continue;
            if (GcdU64(65537ULL, x - 1) != 1ULL) continue;
            return x;
        }
    }

    static UINT128 U128DivMod(UINT128 a, UINT128 b, UINT128* rem_out)
    {
        UINT128 q = MakeU128U64(0);
        UINT128 r = MakeU128U64(0);
        int i;

        for (i = 127; i >= 0; --i)
        {
            r = U128Shl1(r);
            if (U128GetBit(a, i))
            {
                r.lo |= 1ULL;
            }
            if (U128Ge(r, b))
            {
                r = U128Sub(r, b);
                if (i >= 64) q.hi |= (1ULL << (i - 64));
                else q.lo |= (1ULL << i);
            }
        }

        if (rem_out) *rem_out = r;
        return q;
    }

    static UINT128 U128Mod(UINT128 a, UINT128 mod)
    {
        UINT128 r;
        U128DivMod(a, mod, &r);
        return r;
    }

    static UINT128 U128Gcd(UINT128 a, UINT128 b)
    {
        while (!U128IsZero(b))
        {
            UINT128 r = U128Mod(a, b);
            a = b;
            b = r;
        }
        return a;
    }

    struct SIGNED128
    {
        int neg;
        UINT128 mag;
    };

    static SIGNED128 MakeS128(int neg, UINT128 mag)
    {
        SIGNED128 r;
        r.neg = (neg && !U128IsZero(mag)) ? 1 : 0;
        r.mag = mag;
        return r;
    }

    static SIGNED128 S128Neg(SIGNED128 a)
    {
        if (!U128IsZero(a.mag)) a.neg = !a.neg;
        return a;
    }

    static SIGNED128 S128Add(SIGNED128 a, SIGNED128 b)
    {
        SIGNED128 r;
        if (a.neg == b.neg)
        {
            r.neg = a.neg;
            r.mag = U128Add(a.mag, b.mag);
            if (U128IsZero(r.mag)) r.neg = 0;
            return r;
        }

        if (U128Ge(a.mag, b.mag))
        {
            r.neg = a.neg;
            r.mag = U128Sub(a.mag, b.mag);
        }
        else
        {
            r.neg = b.neg;
            r.mag = U128Sub(b.mag, a.mag);
        }

        if (U128IsZero(r.mag)) r.neg = 0;
        return r;
    }

    static SIGNED128 S128Sub(SIGNED128 a, SIGNED128 b)
    {
        return S128Add(a, S128Neg(b));
    }

    static SIGNED128 S128MulU128Small(SIGNED128 a, UINT128 b)
    {
        SIGNED128 r;
        UINT128 acc = MakeU128U64(0);
        UINT128 cur = a.mag;
        int i;

        for (i = 0; i < 128; ++i)
        {
            if (U128GetBit(b, i))
            {
                acc = U128Add(acc, cur);
            }
            if (i != 127) cur = U128Shl1(cur);
        }

        r.neg = a.neg;
        r.mag = acc;
        if (U128IsZero(r.mag)) r.neg = 0;
        return r;
    }

    static UINT128 U128ModInv(UINT128 a, UINT128 mod)
    {
        UINT128 old_r = mod;
        UINT128 r = a;
        SIGNED128 old_t = MakeS128(0, MakeU128U64(0));
        SIGNED128 t = MakeS128(0, MakeU128U64(1));

        while (!U128IsZero(r))
        {
            UINT128 rem;
            UINT128 q = U128DivMod(old_r, r, &rem);
            UINT128 tmp_r = r;
            SIGNED128 tmp_t = t;

            r = rem;
            old_r = tmp_r;

            t = S128Sub(old_t, S128MulU128Small(t, q));
            old_t = tmp_t;
        }

        if (!(old_r.hi == 0 && old_r.lo == 1))
        {
            return MakeU128U64(0);
        }

        if (old_t.neg)
        {
            UINT128 m = U128Mod(old_t.mag, mod);
            if (U128IsZero(m)) return MakeU128U64(0);
            return U128Sub(mod, m);
        }

        return U128Mod(old_t.mag, mod);
    }

    static UINT128 U128ModAdd(UINT128 a, UINT128 b, UINT128 mod)
    {
        UINT128 s = U128Add(a, b);
        if (U128Lt(s, a) || U128Ge(s, mod))
        {
            s = U128Sub(s, mod);
        }
        return s;
    }

    static UINT128 U128ModMul(UINT128 a, UINT128 b, UINT128 mod)
    {
        UINT128 r = MakeU128U64(0);
        int i;

        a = U128Mod(a, mod);

        for (i = 0; i < 128; ++i)
        {
            if (U128GetBit(b, i))
            {
                r = U128ModAdd(r, a, mod);
            }
            if (i != 127)
            {
                a = U128ModAdd(a, a, mod);
            }
        }

        return r;
    }

    static UINT128 PowModU128(UINT128 base, UINT128 exp, UINT128 mod)
    {
        UINT128 r = MakeU128U64(1);
        int i;

        base = U128Mod(base, mod);

        for (i = 0; i < 128; ++i)
        {
            if (U128GetBit(exp, i))
            {
                r = U128ModMul(r, base, mod);
            }
            if (i != 127)
            {
                base = U128ModMul(base, base, mod);
            }
        }

        return r;
    }

    static UINT64 ModInvPrimeU64(UINT64 a, UINT64 p)
    {
        return PowModU64(a, p - 2, p);
    }

    static int GenerateKeyPairInternal(RSAI_PRIVATE* pri, RSAI_PUBLIC* pub, UINT64 seed)
    {
        UINT64 p, q;
        UINT128 n, lambda, e, d;
        UINT128 g;
        UINT64 gcd_pq1;
        UINT128 full_u64_max = MakeU128U64(0xffffffffffffffffULL);

        if (!pri || !pub) return 0;

        SeedU64(seed);
        e = MakeU128U64(65537ULL);

        for (;;)
        {
            p = GeneratePrime63Bit();
            q = GeneratePrime63Bit();
            if (p == q) continue;

            n = Mul64Wide(p, q);

            if (U128Lt(n, full_u64_max) || U128Eq(n, full_u64_max))
            {
                continue;
            }

            gcd_pq1 = GcdU64(p - 1, q - 1);
            lambda = Mul64Wide((p - 1) / gcd_pq1, (q - 1));

            g = U128Gcd(e, lambda);
            if (!(g.hi == 0 && g.lo == 1)) continue;

            d = U128ModInv(e, lambda);
            if (U128IsZero(d)) continue;

            pub->n = n;
            pub->e = e;

            pri->n = n;
            pri->d = d;
            pri->p = p;
            pri->q = q;
            pri->dp = (UINT64)(d.lo % (p - 1));
            pri->dq = (UINT64)(d.lo % (q - 1));
            pri->qinv = ModInvPrimeU64(q % p, p);

            return 1;
        }
    }

    bool GenerateKeyPair(RSAI_PRIVATE* PrivateKeyOut, RSAI_PUBLIC* PublicKeyOut)
    {
        UINT64 seed = ((UINT64)time(NULL) << 32) ^ 0xA5A5A5A55A5A5A5AULL ^ (UINT64)(uintptr_t)PrivateKeyOut;
        return GenerateKeyPairInternal(PrivateKeyOut, PublicKeyOut, seed) ? true : false;
    }

    RSAI_ENCRYPT_DATA Encrypt64(UINT64 Data, const RSAI_PRIVATE& PrivateKey)
    {
        UINT128 m = MakeU128U64(Data);
        UINT128 c = PowModU128(m, PrivateKey.d, PrivateKey.n);

        RSAI_ENCRYPT_DATA out;
        out.hi = c.hi;
        out.lo = c.lo;
        return out;
    }

    UINT64 Decrypt64(RSAI_ENCRYPT_DATA Data, const RSAI_PUBLIC& PublicKey)
    {
        UINT128 c;
        UINT128 m;

        c.hi = Data.hi;
        c.lo = Data.lo;

        m = PowModU128(c, PublicKey.e, PublicKey.n);

        if (m.hi != 0)
            return 0;

        return m.lo;
    }
}

int main()
{
    RsaImport::RSAI_PRIVATE pri;
    RsaImport::RSAI_PUBLIC pub;
    RsaImport::RSAI_ENCRYPT_DATA enc;
    RsaImport::UINT64 plain = 1234567890123456789ULL;
    RsaImport::UINT64 dec;

    if (!RsaImport::GenerateKeyPair(&pri, &pub))
    {
        printf("GenerateKeyPair failed\n");
        return 1;
    }

    printf("public n = ");
    RsaImport::PrintU128Hex(pub.n);
    printf("\n");

    printf("public e = ");
    RsaImport::PrintU128Hex(pub.e);
    printf("\n");

    printf("private d = ");
    RsaImport::PrintU128Hex(pri.d);
    printf("\n");

    enc = RsaImport::Encrypt64(plain, pri);

    printf("plain = %llu\n", (unsigned long long)plain);
    printf("cipher = 0x%016llx%016llx\n",
        (unsigned long long)enc.hi,
        (unsigned long long)enc.lo);

    dec = RsaImport::Decrypt64(enc, pub);

    printf("decrypt = %llu\n", (unsigned long long)dec);

    return 0;
}
