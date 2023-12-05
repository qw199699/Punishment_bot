//	Titile: Simple bots breed social punishment in humans
//	Authors: Chen Shen, Zhixue He, Lei Shi, Zhen Wang, Jun Tanimoto
//  Source code for simulation on the grid lattice network
//	Corresponding: shi lei65@hotmail.com (L.S.);
//  w-zhen@nwpu.edu.cn (Z.W.);
//  tanimoto@cm.kyushu-u.ac.jp (J.T.);

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <ctime>

using namespace std;
#define L 100
#define N L*L
#define RANDOMIZE   3145215
#define str_num  4
#define neig_num  4

/*************************** RNG procedures ****************************************/
#define NN 624
#define MM 397
#define MATRIX_A 0x9908b0df   /* constant vector a */
#define UPPER_MASK 0x80000000 /* most significant w-r bits */
#define LOWER_MASK 0x7fffffff /* least significant r bits */
#define TEMPERING_MASK_B 0x9d2c5680
#define TEMPERING_MASK_C 0xefc60000
#define TEMPERING_SHIFT_U(y)  (y >> 11)
#define TEMPERING_SHIFT_S(y)  (y << 7)
#define TEMPERING_SHIFT_T(y)  (y << 15)
#define TEMPERING_SHIFT_L(y)  (y >> 18)

static unsigned long mt[NN]; /* the array for the state vector  */
static int mti=NN+1; /* mti==NN+1 means mt[NN] is not initialized */
void sgenrand(unsigned long seed)
{int i;
 for (i=0;i<NN;i++) {mt[i] = seed & 0xffff0000; seed = 69069 * seed + 1;
                     mt[i] |= (seed & 0xffff0000) >> 16; seed = 69069 * seed + 1;
  }
  mti = NN;
}
void lsgenrand(unsigned long seed_array[])
{ int i; for (i=0;i<NN;i++) mt[i] = seed_array[i]; mti=NN; }
double genrand() 
{
    unsigned long y;
    static unsigned long mag01[2]={0x0, MATRIX_A};
    if (mti >= NN) 
    {
        int kk;
        if (mti == NN+1) sgenrand(4357); 
        for (kk=0;kk<NN-MM;kk++) {
            y = (mt[kk]&UPPER_MASK)|(mt[kk+1]&LOWER_MASK);
            mt[kk] = mt[kk+MM] ^ (y >> 1) ^ mag01[y & 0x1];
        }
        for (;kk<NN-1;kk++) {
            y = (mt[kk]&UPPER_MASK)|(mt[kk+1]&LOWER_MASK);
            mt[kk] = mt[kk+(MM-NN)] ^ (y >> 1) ^ mag01[y & 0x1];
        }
        y = (mt[NN-1]&UPPER_MASK)|(mt[0]&LOWER_MASK);
        mt[NN-1] = mt[MM-1] ^ (y >> 1) ^ mag01[y & 0x1];
        mti = 0;
    }  
    y = mt[mti++]; y ^= TEMPERING_SHIFT_U(y); y ^= TEMPERING_SHIFT_S(y) & TEMPERING_MASK_B;
    y ^= TEMPERING_SHIFT_T(y) & TEMPERING_MASK_C; y ^= TEMPERING_SHIFT_L(y);
    return y;  
}

double randf(){ return ( (double)genrand() * 2.3283064370807974e-10 ); }
long randi(unsigned long LIM){ return((unsigned long)genrand() % LIM); }

/********************** END of RNG ************************************/

int neighbors[N][neig_num];
int strategy[N];
int type[N];
int learn_type[N];

double payoff_matrix[str_num][str_num];
double gamma,beta,rho,r,conformity_prob;
double K=0.1; 

void generate_grid(void)
{
	for(int i = 0 ; i<N ; i++)
	{
		neighbors[i][0]=i-L;
		neighbors[i][1]=i+L;
		neighbors[i][2]=i-1;
		neighbors[i][3]=i+1;
		if (i<L)                neighbors[i][0]= i + L * (L-1);
		if (i > L * (L - 1) -1) neighbors[i][1]= i - L * (L-1);  
		if (i%L == 0)           neighbors[i][2]= i + L - 1 ;
		if (i%L == L - 1)       neighbors[i][3]= i - L + 1 ;  
	}
} 

void init_game(int bot_type)
{
//	generate the lattice network
	generate_grid();
	
//	initial the payoff matrix
	double temp_m[4][4]={
		{1.0, -r ,1.0, -r-beta},
		{1+r,0,1+r-beta,0},
		{1,-r-gamma,1,-r-gamma-beta},
		{1+r-gamma,0,1+r-beta-gamma,0},
	};
	memcpy(payoff_matrix, temp_m, sizeof(temp_m) );
	
//	initial strategy of agents
	for (int i=0; i<N; i++){
//	in the type array, 0 refer to normal player while 1 refer to the bot
		type[i] = (randf() < rho)? 1:0;
		
		if(type[i] == 1){
			if (bot_type == -1) strategy[i] = randi(str_num);
			else strategy[i] = bot_type;
		}
		else{
//		intial the strategy of normal players
//		value 0 refer to action C, 1 refer to D,  2 refer to CP , and 3 refer to DP
			strategy[i] = randi(str_num);
		}
	}
}

int cal_same_stra(int x){
	int temp_count =0;
	int temp_s = strategy[x];
	for(int i=0; i<neig_num; i++){
		if(strategy[neighbors[x][i]] == temp_s) temp_count++;
	}
	return temp_count;
} 

double cal_payoff(int x, int curr_stra)
{
	double pay = 0;
	int x_str = curr_stra;
	int neig;
	
	for(int i=0; i<neig_num; i++){
		neig = neighbors[x][i];
		pay += payoff_matrix[x_str][strategy[neig]];
	} 
	return pay;
}

void learn_strategy_conformirty(int center)
{
	int temp_count[str_num]={0}; 
	double temp_prob[str_num]={0};
	for(int i=0; i<neig_num; i++) temp_count[strategy[neighbors[center][i]]] ++;
	for(int i=0; i<str_num; i++) temp_prob[i] = (double) temp_count[i]/neig_num;
	
	double prob=0;
	double p = randf();
	for(int i=0; i<str_num; i++){
		prob += temp_prob[i];
		if(p<prob){
			strategy[center] = i;
			break; 
		}
	}
}

void learn_strategy_feimi(int center){
	int neig = neighbors[center][randi(neig_num)];
	double cent_pay = cal_payoff(center,strategy[center]);
	double neig_pay = cal_payoff(neig,strategy[neig]);
	double prob = (double) 1 / ( 1 + exp( (cent_pay-neig_pay)/K ));
	if(randf() <prob) strategy[center] = strategy[neig];
	
}

void learn_strategy_myopic(int center){
	double current_payoff = cal_payoff(center,strategy[center]);
	int target_stra = randi(str_num);
	while(target_stra == strategy[center]) target_stra = randi(str_num);
	double target_payoff = cal_payoff(center, target_stra);
	double prob = (double) 1 / ( 1 + exp( (current_payoff-target_payoff)/K ));
	
	if(randf() <prob) strategy[center] = target_stra;
}


void main_process(void)
{
	int center;
	for(int i=0;i<N;i++){
		center = randi(N);
		if(type[center] == 0){
			
//			Considering the case with fermi rule  and conformity
			if(randf()< conformity_prob ) learn_strategy_conformirty(center); 
			else learn_strategy_feimi(center);
			
//			Considering the case with myopic rule
//			learn_strategy_myopic(center);
		} 
	}
} 

double data_save[10];
void calcu_fraction(void){
	int temp_count[str_num] = {0};
	int num_player=0;
	for(int i=0;i<N;i++){
		if(type[i] == 0){
			num_player ++ ;
			temp_count[ strategy[i] ] ++;
		}
	}
	
	for(int i=0;i<str_num;i++) {
		if(num_player != 0 ) data_save[i] = (double) temp_count[i] / num_player;
	}
}

int main(void) 
{
	sgenrand(time(0));
	
	int MCS_step = 100000;

//	game parametters
	gamma = 0.1;
	beta = 0.3;
	r = 0.25;
	
//	probability of conformity, range [0, 1]
	conformity_prob = 0;
	
//	proportion of bot , range [0, 0.5]
	rho = 0.1;
	
//	value of bot_type to control the action of bot 
//	0 refer to bot adopting action C, 1 refer to D,  2 refer to CP , and 3 refer to DP
//	-1 refer to the bot hold one of four action equally.
	int bot_type = 2;

	

//	initial the game setting
	init_game(bot_type);

	printf(" r = %f rho = %f\t",r,rho);
	
//	MC simulation main process
	for(int i=0; i<MCS_step; i++){
		main_process();
	}
	
	calcu_fraction();
	printf("Finally fraction of action are: F_C= %f F_D= %f F_CP= %f F_DP= %f\n",data_save[0],data_save[1],data_save[2],data_save[3]);
	
	return 0; 
}
