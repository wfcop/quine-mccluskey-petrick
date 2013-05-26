/* Quine-McCluskey-Petrick minimizer
 * by Marcos Jimenez <mj.ecci a+ gmai1 d0+ c0m>
 * copyleft GPL
 * usage: see README
 */

#include <iostream>
#include <iomanip>
#include <sstream>
#include <string>
#include <vector>
#include <algorithm>

using namespace std;

int count1s(size_t x) {
	int o = 0;
	while (x) {
		o += x % 2;
		x >>= 1;
	}
	return o;
}

int vars;

struct Implicant {
	int implicant;
	string minterms;
	vector<int> mints;
	int mask;
	string bits;
	int ones;
	bool used;
	Implicant(int i = 0, vector<int> min = vector<int>(), string t = "", int m = 0, bool u = false)
		: implicant(i), mask(m), ones(0), used(u)
	{
		if (t == "") {
			stringstream ss;
			ss << 'm' << i;
			minterms = ss.str();
		}
		else minterms = t;
		if (min.empty()) mints.push_back(i);
		else mints = min;
		int bit = 1 << vars;
		while (bit >>= 1)
			if (m & bit) bits += '-';
			else if (i & bit) { bits += '1'; ++ones; }
			else bits += '0';
	}
	bool operator<(const Implicant& b) const { return ones < b.ones; }
	vector<int> cat(const Implicant &b) {
		vector<int> v = mints;
		v.insert(v.end(), b.mints.begin(), b.mints.end());
		return v;
	}
	friend ostream &operator<<(ostream &out, const Implicant &im);
};

bool pr = true;
bool fin = true;
ostream &operator<<(ostream &out, const Implicant &im) {
	int bit = 1 << vars, lit = 0;
	ostringstream ss;
	while (bit >>= 1) {
		if (!(im.mask & bit))
			ss << char(lit + 'A') << (im.implicant & bit ? ' ' : '\'');
		++lit;
	}
	if (fin) out << right << setw(16);
	out << ss.str();
	if (pr) out << '\t' << setw(16) << left << im.minterms << ' ' << im.bits << '\t' << im.ones;
	return out;
}

void printTab(const vector<Implicant> &imp) {
	for (size_t i = 0; i < imp.size(); ++i)
		cout << imp[i] << endl;
	cout << "-------------------------------------------------------\n";
}

void mul(vector<size_t> &a, const vector<size_t> &b) {
	vector<size_t> v;
	for (size_t i = 0; i < a.size(); ++i)
		for (size_t j = 0; j < b.size(); ++j)
			v.push_back(a[i] | b[j]);
	sort(v.begin(), v.end());
	v.erase( unique( v.begin(), v.end() ), v.end() );
	for (size_t i = 0; i < v.size() - 1; ++i)
		for (size_t j = v.size() - 1; j > i ; --j) {
			size_t z = v[i] & v[j];
			if ((z & v[i]) == v[i])
				v.erase(v.begin() + j);
			else if ((z & v[j]) == v[j]) {
				size_t t = v[i];
				v[i] = v[j];
				v[j] = t;
				v.erase(v.begin() + j);
				j = v.size();
			}
		}
	a = v;
}

int main() {
	cin >> vars;
	int combs = 1 << vars;
	//bool *minterms = (bool *)calloc(combs, sizeof(bool));

	vector<int> minterms;
	vector<Implicant> implicants;
	for (int mint; cin >> mint; ) {
		implicants.push_back(mint);
		minterms.push_back(mint);
	}
	if (!minterms.size()) { cout << "\n\tF = 0\n"; return 0; }
	sort(minterms.begin(), minterms.end());
	minterms.erase( unique( minterms.begin(), minterms.end() ), minterms.end() );
	if (!cin.eof() && cin.fail()) {	// don't cares
		cin.clear();
		while ('d' != cin.get()) ;
		for (int mint; cin >> mint; )
			implicants.push_back(mint);
	}
	sort(implicants.begin(), implicants.end());
	printTab(implicants);

	vector<Implicant> aux;
	vector<Implicant> primes;
	while (implicants.size() > 1) {
		for (size_t i = 0; i < implicants.size() - 1; ++i)
			for (size_t j = implicants.size() - 1; j > i ; --j)
				if (implicants[j].bits == implicants[i].bits)
					implicants.erase(implicants.begin() + j);
		aux.clear();
		for (size_t i = 0; i < implicants.size() - 1; ++i)
			for (size_t j = i + 1; j < implicants.size(); ++j)
				if (implicants[j].ones == implicants[i].ones + 1 &&
					implicants[j].mask == implicants[i].mask &&
					count1s(implicants[i].implicant ^ implicants[j].implicant) == 1) {
						implicants[i].used = true;
						implicants[j].used = true;
						aux.push_back(
							Implicant(implicants[i].implicant,
							implicants[i].cat(implicants[j]),
							implicants[i].minterms + ',' + implicants[j].minterms,
							(implicants[i].implicant ^ implicants[j].implicant) | implicants[i].mask)
						);
				}
		for (size_t i = 0; i < implicants.size(); ++i)
			if (!implicants[i].used) primes.push_back(implicants[i]);
		implicants = aux;
		sort(implicants.begin(), implicants.end());
		printTab(implicants);
	}
	for (size_t i = 0; i < implicants.size(); ++i)
		primes.push_back(implicants[i]);
	if (primes.back().mask == combs - 1)
		{ cout << "\n\tF = 1\n"; return 0; }

	pr = false;
	bool table[primes.size()][minterms.size()];
	for (size_t i = 0; i < primes.size(); ++i)
		for (size_t k = 0; k < minterms.size(); ++k)
			table[i][k] = false;
	for (size_t i = 0; i < primes.size(); ++i)
		for (size_t j = 0; j < primes[i].mints.size(); ++j)
			for (size_t k = 0; k < minterms.size(); ++k)
				if (primes[i].mints[j] == minterms[k])
					table[i][k] = true;
	for (int k = 0; k < 18; ++k) cout << " ";
	for (size_t k = 0; k < minterms.size(); ++k)
		cout << right << setw(2) << minterms[k] << ' ';
	cout << endl;
	for (int k = 0; k < 18; ++k) cout << " ";
	for (size_t k = 0; k < minterms.size(); ++k)
		cout << "---";
	cout << endl;
	for (size_t i = 0; i < primes.size(); ++i) {
		cout << primes[i] << " |";
		for (size_t k = 0; k < minterms.size(); ++k)
			cout << (table[i][k] ? " X " : "   ");
		cout << endl;
	}
	// Petrick
	vector<size_t> M0, M1;
	for (size_t i = 0; i < primes.size(); ++i)
		if (table[i][0]) M0.push_back(1 << i);
	for (size_t k = 1; k < minterms.size(); ++k) {
		M1.clear();
		for (size_t i = 0; i < primes.size(); ++i)
			if (table[i][k]) M1.push_back(1 << i);
		mul(M0, M1);
	}
	int min = count1s(M0[0]);
	size_t ind = 0;
	// for (size_t i = 0; i < M0.size(); ++i) cout << M0[i] << ','; cout << endl;
	for (size_t i = 1; i < M0.size(); ++i)
		if (min > count1s(M0[i])) {
			min = count1s(M0[i]);
			ind = i;
		}
	fin = false;

	bool f;
	// visualize Petrick results
	cout << "-------------------------------------------------------\n";
	for (size_t j = 0; j < M0.size(); ++j) {
		cout << "\tF = ";
		f = false;
		for (size_t i = 0; i < primes.size(); ++i)
			if (M0[j] & (1 << i)) {
				if (f) cout << " + ";
				f = true;
				cout << primes[i];
			}
		cout << endl;
	}
	cout << "-------------------------------------------------------\n";

	// minimal solution
	cout << "\n\tF = ";
	f = false;
	for (size_t i = 0; i < primes.size(); ++i)
		if (M0[ind] & (1 << i)) {
			if (f) cout << " + ";
			f = true;
			cout << primes[i];
		}
	cout << endl;
}
