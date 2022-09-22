

close all;
clear all;
fx_trace_name='C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project_sign/data/powertrace_fixed_';
rd_trace_name='C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project_sign/data/powertrace_rnd_';
traces= zeros(1001000,751);
cnt=0;
for i=1:2
    str = num2str(i-1)
    str = strcat(str,'.csv');
    sub_traces=csvread(strcat(rd_trace_name,str));
    [m,n]=size(sub_traces)
    traces((cnt+1):(cnt+m), :) = sub_traces;
    cnt=cnt+m;
end
%cnt=cnt-m;
sub_traces=traces((1:cnt),:);
traces=sub_traces;
clear sub_traces

cipher_array=csvread('C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project_sign/MM_vector_spare.csv');
cipher_array=cipher_array((1:cnt),:);



plot(traces(1,:));


plot(traces(30,:));
clear pearson_array_result
clear pearson_eval


HW_matrix= zeros(cnt,70);

for i=1:cnt
    plain_target= cipher_array(i,45)*16777216 + cipher_array(i,46) *65536 +cipher_array(i,47)*256 + cipher_array(i,48);
    for j=1:70
        target= 12070451223 + j-1;
        target2=target*plain_target;
        key_hyp_result=dec2bin(target2);
        target1 = dec2bin(uint32(target2));
        HW_matrix(i,j)=length(find(key_hyp_result=='1'))+length(find(target1=='1'));
    end
end


var_realmeas=traces-mean(traces);
pearson_array_result=zeros(70,n);
row = cnt;

for i=1:70
        res_array=HW_matrix(:,i);
        var_res=res_array-mean(res_array);        
        pearson_cor=((var_res'*var_realmeas)/row)./(std(res_array)*std(traces));
        pearson_array_result(i,:)=pearson_cor;
end

figure();
plot(pearson_array_result');

[max_val,max_ind]=max(max(pearson_array_result));
[sort_max_val,sort_max_ind]=sort(pearson_array_result(:,max_ind));
[min_val,min_ind]=min(min(pearson_array_result));
[sort_min_val,sort_min_ind]=sort(pearson_array_result(:,min_ind));

figure();
hold all;
plot(pearson_array_result(sort_max_ind(1),:));
plot(pearson_array_result(sort_min_ind(70),:));
% 
% cnt=1;
% for i=4:1000:row
%     for j=1:256
%         res_array=HW_matrix(1:i,j);        
%         realmes_array=traces((1:i),1:2000);
%         
%         var_res=res_array-mean(res_array);
%         var_realmeas=realmes_array-mean(realmes_array);
%         
%         pearson_cor=((var_res'*var_realmeas)/i)./(std(res_array)*std(realmes_array));
%         pearson_eval(j,cnt)=max(abs(pearson_cor));
%     end
%     [sort_max_val,sort_max_ind]=sort(abs(pearson_eval(:,cnt)));
%     rank(cnt,1)= 256-find(sort_max_ind==correct_key(1,ind));
%     cnt=cnt+1;
% end
% 
% figure();
% plot(pearson_eval','Color',[0.5 0.5 0.5])
% hold on
% plot(pearson_eval(correct_key(1,ind),:)','r')
% figure();
% plot(rank)
% 
% figure();
% plot(pearson_array_result','Color',[0.5 0.5 0.5])
% hold on
% plot(pearson_array_result(correct_key(1,ind),:)','r')
%     