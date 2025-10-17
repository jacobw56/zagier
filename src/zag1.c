#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>

#define OUTPUT_STYLE 1 /* 0 = print to screen, 1 = write CSV file */

/* --------------- Typedefs --------------- */

/**
 * @brief Laurent polynomial term type
 *
 */
typedef struct
{
    int power;
    mpq_t coeff;
} term_t;

/**
 * @brief Laurent polynomial type
 *
 */
typedef struct
{
    term_t *t;
    int len;
    int cap;
} poly_t;

/* --------------- Helper functions --------------- */

/**
 * @brief Initialize a term to a coefficient of 0/1 and power p.
 *
 * @param[out]  x Polynomial term to be initialized.
 * @param[in]   p Integer power.
 */
static void term_init(term_t *x, int p)
{
    x->power = p;
    mpq_init(x->coeff);
    mpq_set_si(x->coeff, 0, 1);
}

/**
 * @brief Free the memory of a polynomial term.
 *
 * @param[out] x Term to free.
 */
static void term_clear(term_t *x)
{
    mpq_clear(x->coeff);
}

/**
 * @brief Initialize a Laurent polynomial.
 *
 * @param[out] p Polynomial to initialize.
 * @param[in] c Cap
 */
static void poly_init(poly_t *p, int c)
{
    p->len = 0;
    p->cap = (c ? c : 8);
    p->t = malloc(sizeof(term_t) * p->cap);
}

/**
 * @brief Free the memory used for a polynomial.
 *
 * @param p Polynomial to clear.
 */
static void poly_clear(poly_t *p)
{
    for (int i = 0; i < p->len; i++)
    {
        term_clear(&p->t[i]);
    }
    free(p->t);
}

/**
 * @brief Allocate for a polynomial.
 *
 * @param p
 * @param n
 */
static void poly_reserve(poly_t *p, int n)
{
    if (n <= p->cap)
    {
        return;
    }
    while (p->cap < n)
    {
        p->cap *= 2;
    }
    p->t = realloc(p->t, sizeof(term_t) * p->cap);
}

/**
 * @brief Zero a polynomial.
 *
 * @param p
 */
static void poly_zero(poly_t *p)
{
    p->len = 0;
}

/**
 * @brief Add a term to a polynomial
 *
 * @param p     Polynomial to add to.
 * @param pw    Power.
 * @param c     Coefficient.
 * @param min   Minimum power (guard).
 * @param max   Maximum power (guard).
 */
static void poly_add_term(poly_t *p, int pw, mpq_t c, int min, int max)
{
    if (pw < min || pw > max)
        return;
    for (int i = 0; i < p->len; i++)
        if (p->t[i].power == pw)
        {
            mpq_add(p->t[i].coeff, p->t[i].coeff, c);
            return;
        }
    poly_reserve(p, p->len + 1);
    term_init(&p->t[p->len], pw);
    mpq_set(p->t[p->len].coeff, c);
    p->t[p->len].power = pw;
    p->len++;
}

static void poly_add_trunc(poly_t *C, const poly_t *A, const poly_t *B, int min, int max)
{
    poly_zero(C);
    for (int i = 0; i < A->len; i++)
        poly_add_term(C, A->t[i].power, A->t[i].coeff, min, max);
    for (int i = 0; i < B->len; i++)
        poly_add_term(C, B->t[i].power, B->t[i].coeff, min, max);
}

static void poly_mul_trunc(poly_t *C, const poly_t *A, const poly_t *B, int min, int max)
{
    poly_zero(C);
    mpq_t prod;
    mpq_init(prod);
    for (int i = 0; i < A->len; i++)
        for (int j = 0; j < B->len; j++)
        {
            int pw = A->t[i].power + B->t[j].power;
            if (pw < min || pw > max)
                continue;
            mpq_mul(prod, A->t[i].coeff, B->t[j].coeff);
            poly_add_term(C, pw, prod, min, max);
        }
    mpq_clear(prod);
}

/**
 * @brief Copy a polynomial
 *
 * @param[out]  dst Destination polynomial.
 * @param[in]   src Source polynomial.
 */
static void poly_copy(poly_t *dst, const poly_t *src)
{
    poly_clear(dst);
    poly_init(dst, src->cap);
    poly_reserve(dst, src->len);
    for (int i = 0; i < src->len; i++)
    {
        term_init(&dst->t[dst->len], src->t[i].power);
        mpq_set(dst->t[dst->len].coeff, src->t[i].coeff);
        dst->t[dst->len].power = src->t[i].power;
        dst->len++;
    }
}

/**
 * @brief Get the coefficient from the power pw term of a polynomial.
 *
 * @param out
 * @param P
 * @param pw
 */
static void poly_get_coeff(mpq_t out, const poly_t *P, int pw)
{
    mpq_set_si(out, 0, 1);
    for (int i = 0; i < P->len; i++)
        if (P->t[i].power == pw)
        {
            mpq_set(out, P->t[i].coeff);
            return;
        }
}

/**
 * @brief Check if the coefficient is zero by k = 2^r * k_o with k_o odd
 *        and condition k_o <= 2^{r+1} - 5.
 *
 * @param[in]   k   Index of coefficient.
 * @retval  Returns 1 if coefficient is 0, 0 otherwise.
 */
static int bk_is_forced_zero(long long k)
{
    if (k <= 0)
    {
        return 0; // b0 is not forced; we already set b0 = -1/2
    }

    long long r = 0, ko = k;
    while ((ko & 1LL) == 0)
    {
        ko >>= 1;
        r++;
    }

    long long bound = (1LL << (r + 1)) - 5;
    return ko <= bound ? 1 : 0;
}

/* --------------- 2-adic valuation ---------------- */

/**
 * @brief 2-adic valuation on an integer type.
 *
 * @param[out]  out The 2-adic valuation.
 * @param[in]   n   The integer.
 * @retval  Returns 0 on success, 1 if n == 0 (so v2(n) = +infinity).
 */
static int v2_mpz_ll(long long *out, const mpz_t n)
{
    if (mpz_sgn(n) == 0)
    {
        return 1; // v2(0) = +infinity
    }

    mpz_t a;
    mpz_init(a);
    mpz_abs(a, n); // valuation ignores sign

    // mpz_scan1 finds index of least-significant 1 bit -> # of factors of 2
    mp_bitcnt_t tz = mpz_scan1(a, 0);
    *out = (long long)tz;
    mpz_clear(a);

    return 0;
}

/**
 * @brief 2-adic valuation on an rational type.
 *
 * @param[out]  out The 2-adic valuation.
 * @param[in]   q   The rational number.
 * @retval  Returns 0 on success, 1 if n == 0 (so v2(n) = +infinity).
 */
static int v2_mpq_ll(long long *out, const mpq_t q)
{
    if (mpq_sgn(q) == 0)
    {
        return 1; // v2(0) = +infinity
    }

    // Work with a canonicalized copy (den > 0, gcd(num,den)=1)
    mpq_t qc;
    mpq_init(qc);
    mpq_set(qc, q);
    mpq_canonicalize(qc);

    mpz_srcptr num = mpq_numref(qc);
    mpz_srcptr den = mpq_denref(qc);

    long long v_num = 0, v_den = 0;

    // v2(num)
    {
        mpz_t an;
        mpz_init(an);
        mpz_abs(an, num); // num != 0 because q != 0
        mp_bitcnt_t tz = mpz_scan1(an, 0);
        v_num = (long long)tz;
        mpz_clear(an);
    }

    // v2(den)
    {
        // den > 0 by canonicalization; den != 0 for any valid mpq_t
        mp_bitcnt_t tz = mpz_scan1(den, 0);
        v_den = (long long)tz;
    }

    *out = v_num - v_den;
    mpq_clear(qc);

    return 0;
}

/* --------------- Specific recursion ---------------- */
static void build_pj(poly_t *P, mpq_t *b, int j, int min, int max)
{
    poly_zero(P);
    mpq_t one;
    mpq_init(one);
    mpq_set_si(one, 1, 1);
    poly_add_term(P, 1, one, min, max);
    for (int k = 0; k <= j; k++)
        if (mpq_sgn(b[k]) != 0)
            poly_add_term(P, -k, b[k], min, max);
    mpq_clear(one);
}

static void compute_An_of_p(poly_t *A, const poly_t *p, int n, int min, int max)
{
    poly_clear(A);
    poly_init(A, p->cap);
    poly_copy(A, p);
    if (n == 0)
        return;
    poly_t tmp1, tmp2;
    poly_init(&tmp1, p->cap);
    poly_init(&tmp2, p->cap);
    for (int t = 0; t < n; t++)
    {
        poly_mul_trunc(&tmp1, A, A, min, max);
        poly_add_trunc(&tmp2, &tmp1, p, min, max);
        poly_copy(A, &tmp2);
    }
    poly_clear(&tmp1);
    poly_clear(&tmp2);
}

/**
 * @brief Solve for one coefficient.
 *
 * @param bj_out
 * @param b
 * @param j
 * @param n
 */
static void solve_bj(mpq_t bj_out, mpq_t *b, int j, int n)
{
    int T = (1 << n) - j - 1;
    int MAX = (1 << n);
    int MIN = T - (1 << (n + 1));

    poly_t pj, A;
    poly_init(&pj, 64);
    poly_init(&A, 128);

    mpq_t c0, c1, delta, negc0;
    mpq_inits(c0, c1, delta, negc0, NULL);

    mpq_set_si(b[j], 0, 1);
    build_pj(&pj, b, j, MIN, MAX);
    compute_An_of_p(&A, &pj, n, MIN, MAX);
    poly_get_coeff(c0, &A, T);

    mpq_set_si(b[j], 1, 1);
    build_pj(&pj, b, j, MIN, MAX);
    compute_An_of_p(&A, &pj, n, MIN, MAX);
    poly_get_coeff(c1, &A, T);

    mpq_sub(delta, c1, c0);
    if (mpq_sgn(delta) == 0)
    {
        gmp_printf("delta=0 for j=%d (T=%d)\n", j, T);
        exit(1);
    }

    mpq_neg(negc0, c0);
    mpq_div(bj_out, negc0, delta);
    mpq_set(b[j], bj_out);

    mpq_clears(c0, c1, delta, negc0, NULL);
    poly_clear(&pj);
    poly_clear(&A);
}

/* --------------- Main ---------------- */
int main(int argc, char **argv)
{
    int JMAX = (argc > 1) ? atoi(argv[1]) : 10; /* Default to 10 if no argument is given. */
    int n = 0;

    /* Get the value of n from the max coefficient index. */
    while (((1 << (n + 1)) - 3) < JMAX)
    {
        n++;
    }

    printf("Computing up to b[%d] with n=%d (k(n)=%d)\n", JMAX, n, (1 << (n + 1)) - 3);

    mpq_t *b = malloc((JMAX + 1) * sizeof(mpq_t));
    for (int i = 0; i <= JMAX; i++)
    {
        mpq_init(b[i]);
        mpq_set_si(b[i], 0, 1);
    }
    mpq_set_si(b[0], -1, 2); /* Need to init the first one. */

    /* Compute the b_{j} */
    for (int j = 1; j <= JMAX; j++)
    {
        if (bk_is_forced_zero(j))
        {
            mpq_set_si(b[j], 0, 1);
            continue; // skip all heavy work
        }
        solve_bj(b[j], b, j, n);
    }

#if OUTPUT_STYLE == 1
    FILE *f = fopen("b_coeffs.csv", "w");
    if (!f)
    {
        perror("b_coeffs.csv");
        return 1;
    }
    fprintf(f, "k,Numerator,Denominator,2-adic valuation\n");
#endif

    long long v2; // For the 2-adic valuation

    for (int j = 0; j <= JMAX; j++)
    {
        mpz_t num, den;
        mpz_inits(num, den, NULL);
        mpq_get_num(num, b[j]);
        mpq_get_den(den, b[j]);
        // double val = mpq_get_d(b[j]);
#if OUTPUT_STYLE == 0
        if (v2_mpq_ll(&v2, b[j]) == 0)
        {
            gmp_printf("b[%d] = %Qd, v2 = %lld\n", j, b[j], -1 * v2);
        }
        else
        {
            gmp_printf("b[%d] = %Qd, v2 = +infty\n", j, b[j]);
        }
        // gmp_printf("b[%d] = %Qd (%.10f)\n", j, b[j], val);
#else
        if (v2_mpq_ll(&v2, b[j]) == 0)
        {
            gmp_fprintf(f, "%d,%Zd,%Zd,%lld\n", j, num, den, -1 * v2);
        }
        else
        {
            gmp_fprintf(f, "%d,%Zd,%Zd,%lld\n", j, num, den, LLONG_MAX);
        }
        // gmp_fprintf(f, "%d,%Zd,%Zd,%.15f\n", j, num, den, val);
#endif
        mpz_clears(num, den, NULL);
    }

#if OUTPUT_STYLE == 1
    fclose(f);
    printf("CSV written to b_coeffs.csv\n");
#endif

    for (int i = 0; i <= JMAX; i++)
    {
        mpq_clear(b[i]);
    }
    free(b);

    return 0;
}
