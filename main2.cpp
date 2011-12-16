#include <iostream>
#include <cstdio>
#include <string>
#include <algorithm>
#include <cstring>
#include <numeric>
#include <cmath>
#include <vector>
#include <deque>
#include <cstdlib>

using namespace std;
 
#define MAX_WIDTH 50
#define MAX_HEIGHT 50
#define X first
#define Y second
#define PB push_back
#define MP make_pair
#define MAX_TIME 100000
#define INF 1e+10
#define dump(x)  cerr << #x << " = " << (x) << endl;

class Tower{
public:
    Tower(int p, int q, int r, int s){
        x = p; y = q; a = r; c = s;
    }
        
    int x; //position
    int y; //position
    int a; //times enhanced
    int c; //kind of this: 0-rapid 1-attack 2-freeze
};
 
class Enemy{
public:
    Enemy(int a, int b, int c, int d, int e){
        x = a;
        y = b;
        t = c;
        l = d;
        s = e;
    }
        
    int x;
    int y;
    int t;
    int l;
    int s;
};
 
class Inst{
public:
    Inst(int p, int q, int r, int s){
        x = p;
        y = q;
        e = r;
        k = s;
    }
    int x;
    int y;
    int e;
    int k;
};

class Source{
public:
    Source(int a, int b, double c){
        x = a;
        y = b;
        d = c;
    }
    int x;
    int y;
    double d;

    bool operator <(const Source arg) const{
        return d < arg.d;
    }
};

int dx[8] = {0,-1,-1,-1,0,1,1,1};
int dy[8] = {1,1,0,-1,-1,-1,0,1};

int S;                               //マップの数
int L;                               //マップごとのレベルの数
int W,H;                             //マップの広さ、高さ
int LIFE;                            //残りライフ
int M;                               //残り資金
int T;                               //タワーの数
int E;                               //敵の数
int mapnum,levelnum;
char f[MAX_HEIGHT][MAX_WIDTH];   //マップ
double d[MAX_HEIGHT][MAX_WIDTH]; //ある始点からBFSしたときの距離
double min_distance[100][100];   //頂点数よくわからない
bool v[MAX_HEIGHT][MAX_WIDTH];   //BFS時のvisited保持
vector<Tower> towers;                //Towerの集合
vector<Enemy> enemies;               //Enemyの集合
vector<Inst> inst;                   //output用
vector<Inst> tmpinst;
vector<Inst> addinst;
vector<Source> source;               //敵生成場所
vector<Source> sink;                 //敵目的地
string str;


//二点間の位置関係を求める関数
//前者からみた後者がdx,dyのどれにあたるかを返す
//321
//4x0
//567
int calc_direction(int x1, int y1, int x2, int y2){
    if(x1 == x2){
        if(y1 < y2){
            return 0;
        }else{
            return 4;
        }
    }else if(y1 == y2){
        if(x1 < x2){
            return 6;
        }else{
            return 2;
        }
    }else{
        if(x1 > x2){
            if(y1 < y2){
                return 1;
            }else{
                return 3;
            }
        }else if(x1 < x2){
            if(y1 < y2){
                return 7;
            }else{
                return 5;
            }
        }
    }
    return -1;
}

//BFSで距離をもとめる
void calc_dst_from(int x, int y){
    deque<pair<int, int> > q;
    pair<int,int> cur;
    int nxt_x, nxt_y;
    memset(v,false,sizeof(v));
    fill((double *)d, (double *)d+(MAX_HEIGHT)*(MAX_WIDTH), 1e+10);

#ifdef DEBUG_BOARD
    for(int i=0;i<H;i++){
        for(int j=0;j<W;j++){
            cout << f[i][j];
        }
        cout << endl;
    }
#endif
    v[x][y] = true;
    d[x][y] = 0;
    q.PB(MP(x,y));
    while(!q.empty()){
        cur = q.front(); q.pop_front();
#ifdef DEBUG_BFS
        dump(cur.X);
        dump(cur.Y);
#endif
        for(int i=0;i<8;i+=2){
            nxt_x = cur.X + dx[i];
            nxt_y = cur.Y + dy[i];
            if(f[nxt_x][nxt_y] != 't' && f[nxt_x][nxt_y] != '1' &&
               v[nxt_x][nxt_y] == false){
                d[nxt_x][nxt_y] = min(d[nxt_x][nxt_y], d[cur.X][cur.Y] + 1);
                v[nxt_x][nxt_y] = true;
                q.PB(MP(nxt_x, nxt_y));
#ifdef DEBUG_BFS
                dump(nxt_x);
                dump(nxt_y);
#endif
            }
        }
        for(int i=1;i<8;i+=2){
            nxt_x = cur.X + dx[i];
            nxt_y = cur.Y + dy[i];
            if(f[nxt_x][nxt_y] != 't' && f[nxt_x][nxt_y] != '1' &&
               f[cur.X][nxt_y] != 't' &&
               f[cur.X][nxt_y] != '1' &&
               f[nxt_x][cur.Y] != 't' &&
               f[nxt_x][cur.Y] != '1' &&
               v[nxt_x][nxt_y] == false){
                d[nxt_x][nxt_y] = min(d[nxt_x][nxt_y], d[cur.X][cur.Y] + 1.4);
                v[nxt_x][nxt_y] = true;
                q.PB(MP(nxt_x, nxt_y));
#ifdef DEBUG_BFS
                dump(nxt_x);
                dump(nxt_y);
#endif
            }
        }
    }
#ifdef DEBUG_BFS
    for(int i=0;i<H;i++){
        for(int j=0;j<W;j++){
            if(d[i][j] != 1e+10){
                printf("%.1lf ", d[i][j]);
            }else{
                printf("INF ");
            }
        }
        printf("\n");
    }
#endif
}

//与えられた座標からいずれかのsinkへ道があるかどうか調べる関数
bool is_reachable(int x, int y){
    calc_dst_from(x,y);
    for(int i=0;i<sink.size();i++){
        if(d[sink[i].x][sink[i].y] != 1e+10){
            return true;
        }
    }
    return false;
}

//引数:始点とするsourceのindex
//返値:いずれか1つのsinkに到達できればtrue
//副作用としてmin_distance[index][hoge]にその距離を保持
bool is_reachable_from_source(int index){
	bool ret=false;
	
	//BFSして計算
	calc_dst_from(source[index].x, source[index].y);
	//この時点でdに各到達可能セルへの最短経路の値が入っている
	for(int i=0;i<sink.size();i++){
		min_distance[index][i] = d[sink[i].x][sink[i].y];
		if(min_distance[index][i] != INF){ //i-thの sink に到達可能な場合
			ret = true;
		}
	}
	return ret;
}


//返値:有効な盤面であるかどうか(∀source ∃reachable-sink)
bool whole_reachable2(void){
	int ret = true;
	
	//全てのsourceから
	for(int i=0;i<source.size();i++){
		if(!is_reachable_from_source(i)){
			//いずれのsinkにも到達できないsourceが存在する場合無効な盤面、
			//この時点でreturn可能だが、そうでない場合の最短路の計算のため
			//returnしない
			ret = false;
		}
	}
	return ret;
}

bool whole_reachable(void){
    //for each source
    for(int i=0;i<source.size();i++){
        bool isok = false;
        calc_dst_from(source[i].x,source[i].y);
        for(int j=0;j<sink.size();j++){
            min_distance[i][j] = d[sink[j].x][sink[j].y];
            if(d[sink[j].x][sink[j].y] != 1e+10){
                isok = true;
                break;
            }
        }
        if(!isok) return false;
        /*
          if(!is_reachable(source[i].x,source[i].y)) return false;
        */
    }
    return true;
}

void disable_sink(void){
#ifdef DEBUG_DISABLE
    dump(sink.size());
#endif
    if(sink.size() == 1) return;
    //sinkの距離をリセット
    for(int i=0;i<sink.size();i++)
        sink[i].d = 1e+10;
  
    //各sourceからdfsする
    for(int i=0;i<source.size();i++){
        calc_dst_from(source[i].x, source[i].y);
        for(int j=0;j<sink.size();j++){
            sink[j].d = min(sink[j].d, d[sink[j].x][sink[j].y]);
        }
    }

    //sort
    sort(sink.begin(), sink.end());

    vector<pair<int,int> > cand;
    for(int i=0;i<sink.size()-1;i++){
        cand.clear();
        for(int j=0;j<8;j+=2){
            if(f[sink[i].x + dx[j]][sink[i].y + dy[j]] == '0'){
                cand.PB(MP(sink[i].x + dx[j],sink[i].y + dy[j]));
            }
        }
        if(M >= cand.size() * 10){
            //塞ぐことができる
            for(int j=0;j<cand.size();j++){
                //試しに塞いでみる
                f[cand[j].X][cand[j].Y] = 't';
            }
            //到達できないとまずいので戻す
            if(!whole_reachable){
                for(int j=0;j<cand.size();j++){
                    f[cand[j].X][cand[j].Y] = '0';
                }
            }else{
                for(int j=0;j<cand.size();j++){
                    if(mapnum >= 3){
                        inst.PB(Inst(cand[j].X, cand[j].Y, 3, 0));
                    }else{
                        inst.PB(Inst(cand[j].X, cand[j].Y, 0, 0));
                    }
                }
            }
        }else{
            break;
        }
    }
    return;
}

//manhattan-dist
int manh_dst(int x1,int y1, int x2, int y2){
    return abs(x1 - x2) + abs(y1 - y2);
}

//main routine(obsolate)
void AI(){
    double heu[source.size()];
    vector<int> times[source.size()];
    memset(heu,0,sizeof(heu));

    //stage個別対応
    if(mapnum == 0){
        if(levelnum == 5){
            inst.PB(Inst(2,4,0,1));
            inst.PB(Inst(3,4,1,1));
            inst.PB(Inst(4,4,0,1));
            inst.PB(Inst(5,4,0,1));
        }else if(levelnum == 6){
            inst.PB(Inst(5,4,1,1));
        }
    }else if(mapnum == 1){
        if(levelnum == 0){
            inst.PB(Inst(3,4,3,1));
            inst.PB(Inst(5,4,4,1));
        }
    }else if(mapnum == 2){
        if(levelnum == 0){
            inst.PB(Inst(4,4,4,1));
            inst.PB(Inst(7,3,4,2));
            inst.PB(Inst(7,5,4,2));
        }
    }
 
    if(levelnum == 0){
        disable_sink();
    }
    for(int i=0;i<source.size();i++){
        source[i].d = 0;
    }
  
    //heuristic
    //敵の重要度I=life/移動にかかる時間
    //(はやいほど、lifeが多いほど影響は大きい)
    //各sourceごとに出現時刻の分散σを計算する
    //const*exp(-1*σ)*sum(I)->砲台の必要度
    //砲台ごとに値を設定し、必要度に応じて
    //配置すればいい？
    for(int i=0;i<enemies.size();i++){
        for(int j=0;j<source.size();j++){
            if(enemies[i].x == source[j].x && enemies[i].y == source[j].y) break;
            heu[j] += (double)enemies[i].l / enemies[i].s;
            times[j].PB(enemies[i].t);
        }
    }
    //それぞれのsourceについて分散を求めてheuを更新
    for(int i=0;i<source.size();i++){
        double ave=0;
        double div=0;
        if(times[i].size() != 0){
            ave = (double)accumulate(times[i].begin(), times[i].end(), 0) / times[i].size();
            //cerr << ave << endl;
            for(int j=0;j<times[i].size();j++){
                div += pow(times[i][j] - ave, 2);
                //cerr << div << endl;
            }
            div /= times[i].size();
            heu[i] *= exp(-1 * div);
        }
        source[i].d = heu[i];
#ifdef DEBUG_PARAM
        cout << source[i].d << endl;
#endif
    }

    //既に設置されているタワーの分ずつ減らしていく
    for(int i=0;i<towers.size();i++){
        int range;
        int power;
        //値は適当
        if(towers[i].c == 0){
            range = 4;
            power = 1;
        }else if(towers[i].c == 1){
            range = 5;
            power = 1;
        }else{
            range = 2;
            power = 1;
        }
        for(int j=0;j<source.size();j++){
            if(manh_dst(towers[i].x, towers[i].y, source[j].x, source[j].y) <= range){
                source[j].d -= power;
            }
        }
    }

    sort(source.begin(), source.end());
    reverse(source.begin(),source.end());

    int loop_count = 0;
    while(1){
        for(int i=0;i<8 && M >= 20;i++){
            if(f[source[0].x + dx[i]][source[0].y + dy[i]] == '0'){
                //とりあえず置いてみて、道があるかどうか調べる
                f[source[0].x + dx[i]][source[0].y + dy[i]] = 't';
                if(!is_reachable(source[0].x, source[0].y)){
                    f[source[0].x + dx[i]][source[0].y + dy[i]] = '0';
                    loop_count++;
                }else{
                    if(M >= 20){
                        if(mapnum <= 1){
                            inst.PB(Inst(source[0].x + dx[i],source[0].y + dy[i], 0,1));
                        }else if(mapnum >= 2){
                            inst.PB(Inst(source[0].x + dx[i],source[0].y + dy[i], 3,1));
                        }
                        M -= 20;
                        source[0].d -= 1;
                        loop_count = 0;
                        break;
                    }
                }
            }
        }
        sort(source.begin(), source.end());
        reverse(source.begin(),source.end());
        if(source[0].d < 0 || loop_count > 8 * source.size()) break;
    }
}	  

//output determined towers
void output(void){
	printf("%d\n",inst.size());
	
	//Twitterで見かけた情報から
	//readlineが走ってしまう対策
	if(inst.size() == 0){
		printf("\n");
		return;
	}
    for(int i=0;i<inst.size();i++){
        printf("%d %d %d %d\n", inst[i].y, inst[i].x, inst[i].e, inst[i].k);
    }
    inst.clear();
    return;
}


//俺俺乱択
//いずれかのsource-sink pathの経路が延びるなら置く
void AI2(){
    double prev_min[source.size()][sink.size()];
    double after_min[source.size()][sink.size()];

#ifdef DEBUG_RANDOM
    cout << "run AI2" << endl;
#endif
    
    //stage個別対応
    //別ルーチンが走らないので
    //全レベルこっちにするなら追加が必要
    if(mapnum == 0){
        if(levelnum == 5){
            inst.PB(Inst(2,4,0,1));
            inst.PB(Inst(3,4,1,1));
            inst.PB(Inst(4,4,0,1));
            inst.PB(Inst(5,4,0,1));
        }else if(levelnum == 6){
            inst.PB(Inst(5,4,1,1));
        }
    }else if(mapnum == 1){
        if(levelnum == 0){
            inst.PB(Inst(3,4,3,1));
            inst.PB(Inst(5,4,4,1));
        }
    }else if(mapnum == 2){
        if(levelnum == 0){
            inst.PB(Inst(4,4,4,1));
            inst.PB(Inst(7,3,4,2));
            inst.PB(Inst(7,5,4,2));
        }
    }
    //一度最短経路を計算しておく
    whole_reachable2();
    for(int i=0;i<source.size();i++){
        for(int j=0;j<sink.size();j++){
            prev_min[i][j] = min_distance[i][j];
        }
    }
    double rate = 9;
    int loop_count=0;     //連続して失敗した試行数、一定以上で終了
    int count = 0;        //置いた砲台の数
    int phase = 0;//0:=最短経路の改善が1以上でないと置かない 1:=そうでなくても置く

    if(mapnum <= 8){
        rate = 30;
    }else if(mapnum < 40){
        rate = 40;
    }else{
        rate = 3;
    }

  BEGIN_RAND:
    while(loop_count <= (H-2)*(W-2)*50 && count <= (H-2) * (W-2) / rate){ //thresholdは適当
        //ランダムに選んでいずれかのsinkへの距離の最小値が大きくなる場合は置く
        //while前に全source-sink間で最短経路を計算
        //randomize時に1回計算
        //置くなら　　->更新
        //置かないなら->そのまま

        int candx, candy; 
        int kind = 0;         //設置する砲台の種類 
        int level = -1;       //設置する砲台のレベル
        candx = (rand() % (H-2)) + 1;
        candy = (rand() % (W-2)) + 1;

        //置けなかったらやりなおし
        if(f[candx][candy] != '0'){
            loop_count++;
            continue;
        }

        //設置してみる
        f[candx][candy] = 't';
        //道が存在しなければ不可
        if(!whole_reachable2()){
            f[candx][candy] = '0';
            loop_count++;
        }else{
            bool isok = false;
            for(int i=0;i<sink.size();i++){
                for(int j=0;j<source.size();j++){
                    if(phase == 0){
                        if(min_distance[j][i] - prev_min[j][i] >= 1){
                            //どこか1ルートでも最短経路が延びていれば置く
                            isok = true;
                            /*
                              if(min_distance[j][i] <= 5){
                              kind = 1;
                              }
                            */
                        }
                    }else{
                        if(min_distance[j][i] - prev_min[j][i] > 0){
                            isok = true;
                        }
                    }
                }
            }
            if(isok){
                //確定させる
                if(mapnum <= 2){
                    inst.PB(Inst(candx,candy,0,kind));
                }else if(mapnum == 3){
                    inst.PB(Inst(candx,candy,1,kind));
                }else{
                    if(kind != 1){
                        if(mapnum < 39){
                            inst.PB(Inst(candx,candy,0,kind));
                        }else{
                            inst.PB(Inst(candx,candy,4,kind));
                        }
                        /*
                          if(mapnum <= 9 || mapnum == 16 || rand()%8 != 7){
                          inst.PB(Inst(candx,candy,2,kind));
                          }else{
                          inst.PB(Inst(candx,candy,1,kind));
                          }
                        */
                    }else{
                        inst.PB(Inst(candx,candy,0,kind));
                    }
                }
                count++;
                loop_count = 0;
                for(int i=0;i<source.size();i++){
                    for(int j=0;j<sink.size();j++){
                        prev_min[i][j] = min_distance[i][j];
                    }
                }
#ifdef DEBUG_RANDOM
                cout << "put" << endl;
#endif
            }else{
                f[candx][candy] = '0';
            }
        }
    }
    if(phase == 0 && count <= (H-2)*(W-2)/rate){
        phase = 1;
        loop_count = 0;
        goto BEGIN_RAND;
    }
}

//全sourceの回りに最大強化ラピッドを置く
void AI3(void){
    for(int i=0;i<source.size();i++){
        for(int j=0;j<8;j++){ //全ての隣接セルについて
            //置けなかったら諦める
            if(f[source[i].x + dx[j]][source[i].y + dy[j]] != '0') continue;
            //おいてみる
            f[source[i].x + dx[j]][source[i].y + dy[j]] = 't';
            //到達不可能であれば
            if(!whole_reachable()){
                f[source[i].x + dx[j]][source[i].y + dy[j]] = '0'; //戻す
            }else{
                inst.PB(Inst(source[i].x + dx[j], source[i].y + dy[j], 4, 0));
                break;
            }
        }
    }
}

//全sourceの回りに最大強化ラピッドを2個置く
void AI4(void){
    bool flag = false;
    for(int i=0;i<source.size();i++){
        for(int j=0;j<8;j++){ //全ての隣接セルについて
            //置けなかったら諦める
            if(f[source[i].x + dx[j]][source[i].y + dy[j]] != '0') continue;
            //おいてみる
            f[source[i].x + dx[j]][source[i].y + dy[j]] = 't';
            //到達不可能であれば
            if(!whole_reachable()){
                f[source[i].x + dx[j]][source[i].y + dy[j]] = '0'; //戻す
            }else{
                inst.PB(Inst(source[i].x + dx[j], source[i].y + dy[j], 4, 0));
                if(flag == false){
                    flag = true;
                }else{
                    flag = false;
                    break;
                }
            }
        }
    }
}

//全sourceと全sinkの回りに置けるだけおく
void AI5(void){
    for(int i=0;i<source.size();i++){
        for(int j=0;j<8;j++){ //全ての隣接セルについて
            //置けなかったら諦める
            if(f[source[i].x + dx[j]][source[i].y + dy[j]] != '0') continue;
            //おいてみる
            f[source[i].x + dx[j]][source[i].y + dy[j]] = 't';
            //到達不可能であれば
            if(!whole_reachable()){
                f[source[i].x + dx[j]][source[i].y + dy[j]] = '0'; //戻す
            }else{
                inst.PB(Inst(source[i].x + dx[j], source[i].y + dy[j], 4, 0));
            }
        }
    }
    for(int i=0;i<sink.size();i++){
        for(int j=0;j<8;j++){ //全ての隣接セルについて
            //置けなかったら諦める
            if(f[sink[i].x + dx[j]][sink[i].y + dy[j]] != '0') continue;
            //おいてみる
            f[sink[i].x + dx[j]][sink[i].y + dy[j]] = 't';
            //到達不可能であれば
            if(!whole_reachable()){
                f[sink[i].x + dx[j]][sink[i].y + dy[j]] = '0'; //戻す
            }else{
                inst.PB(Inst(sink[i].x + dx[j], sink[i].y + dy[j], 4, 0));
            }
        }
    }
}

//マップ40以降はこのルーチンを使う
//返り値:source-sink間の最短経路の最小値
double random_after40(){
    double prev_min[source.size()][sink.size()];
    double after_min[source.size()][sink.size()];
    double ret = 1 << 30;

    tmpinst.clear();

#ifdef DEBUG_RANDOM
    cout << "run random after lvl 40" << endl;
#endif
    
    //一度最短経路を計算しておく
    whole_reachable2();
    for(int i=0;i<source.size();i++){
        for(int j=0;j<sink.size();j++){
            prev_min[i][j] = min_distance[i][j];
        }
    }
    double rate = 5;
    int loop_count=0;     //連続して失敗した試行数、一定以上で終了
    int count = 0;        //置いた砲台の数
    int phase = 0;//0:=最短経路の改善が1以上でないと置かない 1:=そうでなくても置く

BEGIN_RAND:
    while(loop_count <= (H-2)*(W-2)*50 && count <= (H-2) * (W-2) / rate){ //thresholdは適当
        //ランダムに選んでいずれかのsinkへの最短経路が長くなる場合は置く
        //while前に全source-sink間で最短経路を計算
        //randomize時に1回計算
        //置くなら　　->更新
        //置かないなら->そのまま

        int candx, candy; 
        int kind = 0;         //設置する砲台の種類 
        int level = -1;       //設置する砲台のレベル
        candx = (rand() % (H-2)) + 1;
        candy = (rand() % (W-2)) + 1;

        //置けなかったらやりなおし
        if(f[candx][candy] != '0'){
            loop_count++;
            continue;
        }

        //設置してみる
        f[candx][candy] = 't';
        //道が存在しなければ不可
        if(!whole_reachable2()){
            f[candx][candy] = '0';
            loop_count++;
        }else{
            bool isok = false;
            for(int i=0;i<sink.size();i++){
                for(int j=0;j<source.size();j++){
                    if(phase == 0){
                        if(min_distance[j][i] - prev_min[j][i] >= 1){
                            isok = true;
                        }
                    }else{
                        if(min_distance[j][i] - prev_min[j][i] > 0){
                            isok = true;
                        }
                    }
                }
            }
            if(isok){
                //確定させる
                tmpinst.PB(Inst(candx,candy,4,kind));
                count++;
                loop_count = 0;
                for(int i=0;i<source.size();i++){
                    for(int j=0;j<sink.size();j++){
                        prev_min[i][j] = min_distance[i][j];
                    }
                }
#ifdef DEBUG_RANDOM
                cout << "put" << endl;
#endif
            }else{
                f[candx][candy] = '0';
            }
        }
    }
    if(phase == 0 && count <= (H-2)*(W-2)/rate){
        phase = 1;
        loop_count = 0;
        goto BEGIN_RAND;
    }

    //returnのための値更新
    for(int i=0;i<source.size();i++){
        for(int j=0;j<sink.size();j++){
            ret = min(ret, prev_min[i][j]);
        }
    }
    return ret;
}

void disable_inst(vector<Inst> &arg){
    int x,y;
    for(int i=0;i<arg.size();i++){
        x = arg[i].x;
        y = arg[i].y;
        f[x][y] = '0';
    }
}

void enable_inst(vector<Inst> &arg){
    int x,y;
    for(int i=0;i<arg.size();i++){
        x = arg[i].x;
        y = arg[i].y;
        f[x][y] = 't';
    }
}

int main(void){
#ifdef DEBUG
    cout << "running in debug mode" << endl;
#endif

    srand(time(NULL));

    cin >> S;
    for(mapnum = 0; mapnum < S; mapnum++){
#ifdef DEBUG
        dump(mapnum);
#endif
        cin >> W >> H;
        //initialize
        source.clear();
        sink.clear();
        //region read map
        for(int i=0;i<H;i++){
            cin >> str;
            for(int j=0;j<W;j++){
                f[i][j] = str[j];
                if(f[i][j] == 's'){
                    source.PB(Source(i,j,1e+10));
                }
                if(f[i][j] == 'g'){
                    sink.PB(Source(i,j,1e+10));
                }
            }
        }
        //endregion read map
        cin >> L;
        cin >> str; //expected "END" for each map
        if(str != "END"){
            cout << "[main]invalid data on the end of read map" << endl;
            return -1;
        }
                
        for(levelnum = 0; levelnum < L; levelnum++){
            cin >> LIFE >> M >> T >> E;
            //region read tower data
            towers.clear(); //initialized towers
            for(int i=0;i<T;i++){
                int x,y,a,c;
                cin >> x >> y >> a >> c;
                //set each tower to field
                f[x+1][y+1] = 't';
                towers.PB(Tower(x,y,a,c));
            }
            //endregion read tower data
                        
            //region read enemy data
            enemies.clear();
            for(int i=0;i<E;i++){
                int x,y,t,l,s;
                cin >> x >> y >> t >> l >> s;
                enemies.PB(Enemy(x,y,t,l,s));
            }
            //endregion read enemy data
                        
            cin >> str; //expected "END"
            if(str != "END"){
                cout << "[main]invalid data on the end of read level" << endl;
                return -1;
            }
            //region AI
            if(mapnum <= 2){
                AI();
            }else if(levelnum == 0){
                if(mapnum < 40){
                    AI4();
                    AI2();
                }else{
                    //AI4();
                    double dist = 0, candidate;
                    for(int i=0;i<3;i++){
                        candidate = random_after40();
#ifdef DEBUG_AFTER_40
                        printf("candidate = %lf\n", candidate);
#endif
                        //この時点でtmpinstとして置いたように盤面が変わっているので戻す
                        disable_inst(tmpinst);
                        if(dist < candidate){
                            dist = candidate;
                            addinst = tmpinst;
#ifdef DEBUG_AFTER_40
                            printf("# of inst = %d\n", inst.size());
                            printf("# of tmpinst = %d\n", tmpinst.size());
#endif
                        }
                    }
                    for(int i=0;i<addinst.size();i++){
                        inst.PB(addinst[i]);
                    }
#ifdef DEBUG_AFTER_40
                    printf("# of tower = %d\n", inst.size());
#endif
                    enable_inst(inst);
                }
            }
            output();
            //endregion  AI
        } //end of a level
    }// end of a map
}
