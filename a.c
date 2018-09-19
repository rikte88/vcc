int main()
{
	int	a;
	int	b;
	int	c;
	int	d;
	int	i;
	int	ii;
	int	j;
	int	jj;
	int	k;
	int	m;
	int	n;
	int	p;
	int	q;
	int	r;
	int	s;
	int	t;
	int	u;
	int	v;
	int	w;
	int	x;
	int	y;
	int	z;
	
	a = get();
	b = get();
	x = get();
	c = get();
	d = get();

	z = 1;
	k = 2;
	s = 3;
	y = 4;

	u = 1;

	goto L1;

	u = 1 / u;

L1:	
	u = u + 2;
	if (a < b) {
		u = u + 4;
		goto L3;
	} else {
		u = u + 8;
		goto L2;
	}
L2:	
	u = u + 16;
	if (c < d) {
		u = u + 32;
		goto L6;
	} else {
		u = u + 64;
		goto L3;
	}

L3:	
	u = u + 128;
	goto L4;

L4:	
	u = u + 256;
	goto L5;

L6:
	u = u + 512;
	goto L7;

L7:
	u = u + 1024;
	goto L5;

L5:
	u = u + 2048;

	put(u);
	v = 0;
	u = 0;
	i = 0;
	j = 0;

	while (v < x) {
		u = u + b * c;
		u = u + b * d * c;
		u = u / 2;
		u = u + c * b;
		u = u + b * d * c;
		u = u / 4;
		u = u + c * c;
		u = u + b * d * c;
		u = u / 8;
		u = u + b * b;
		u = u + b * d * d;
		u = u / 16;
		i = i + 1;
		j = i;

		i = 2;
		j = 3 * i;
		i = j * 4;	
		j = i / 5;
		y = y + j * i;

		u = - -u;
		k = u - u;
		m = 1 + k + u + 2;
		n = 2 * u * 3;
		p = (m*n) * (m*n) * (m*n) * (m*n) * (m*n) * (m*n) * (m*n) * (m*n) * (m*n) * (m*n);
		q = m*n*p*m*n*p*m*n*p*m*n*p*m*n*p*m*n*p*m*n*p*m*n*p*m*n*p*m*n*p;
			
		r = 0;
		s = 0;
		while (s < 100) {
			r = r + (a+b) + (b+a) + (a+a) + (b+b);
			s = s + 1;
		}
	
		r = r + 1;
		r = r + 1;
		r = r + 1;
		r = r + 1;
	
		if (r != 0) {
			z = 0;
			s = 0;
			while (s < 100) {
				z = z + p * q * r;
				s = s + 1;
			}
		
			r = r + 1;
			r = 0;
		}

		if (r != 0)
			r = p + q;

		if (a < b) {
			z = 1;
			t = 99;
		if (a >= b)
			z = 2;
			t = 98;
		}

		i = 0;
		while (i < 10) {
			j = 0; 
			while (j < 10) {
				z = z + a / b * c;
				j = j + 1;
			}
			i = i + 1;	
		}
		
		if (u < j)
			u = -u * z;
		if (c < 0)
			c = -c / z;
		w = 0;

		while (w < b) {
			c = b + a + c * d;
			u = u - c;
			k = 0;
			while (k < i * j)
				k = k + a * i * j - b;

			while (k < i * j * 10)
				if (i + j == a)
					k = k * a * i * j + b;
				else
					k = k / a * i * j + b + 1;
				k = k + (z == (i * j)) * a * b * c * d / u;
			w = w + 1;
		}

		v = v + 1;
		ii = i;
		k = k / 2000;

		while (ii < 100) {
			jj = v * ii + w;
			s  = s + jj;
			ii = ii + k;
		}
	}
	
	put(u);
	put(a);
	put(b);
	put(c);
	put(d);
	put(k);
	put(s);
	put(y);

	return 0;
}
