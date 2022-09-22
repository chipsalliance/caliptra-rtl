% intermediate_file='C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_masked_arith/math_model/results/mask_result.csv';
% intermediate=csvread(intermediate_file);
% [m,n]=size(intermediate);
% intermediate = intermediate(2:m,:);
% intermediate = intermediate(:,2:n);
% plot(intermediate(1:1000,:))

a = zeros(1,13000);
for i =1:13000
    if i<=8000
        a(1,i)=0;
    else
        a(1,i)=1;
    end
end
[counts,centers] = hist(a)
bar(centers,counts)